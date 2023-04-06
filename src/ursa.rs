use crate::{join, platform};
use arrayref::array_ref;
use arrayvec::ArrayVec;
use core::cmp;

/// Block size for Ursa's proof of delivery. Which is 256KiB. This number is in Blake3
/// chunks and the code is implemented assuming this is always a power of two.
const URSA_BLOCK_SIZE_IN_CHUNK_LOG_2: usize = 8;
const URSA_BLOCK_SIZE_IN_CHUNK: usize = 1 << URSA_BLOCK_SIZE_IN_CHUNK_LOG_2;
const URSA_BLOCK_SIZE_BYTES: usize = URSA_BLOCK_SIZE_IN_CHUNK * crate::CHUNK_LEN;
const URSA_BLOCK_SIZE_IN_CHUNK_MOD_MASK: u64 = (URSA_BLOCK_SIZE_IN_CHUNK - 1) as u64;
const URSA_MAX_TREE_DEPTH: usize = crate::MAX_DEPTH - URSA_BLOCK_SIZE_IN_CHUNK_LOG_2;

pub struct HasherWithTree {
    tree: Vec<[u8; 32]>,
    block_state: BlockState,
    cv_stack: ArrayVec<crate::CVBytes, { URSA_MAX_TREE_DEPTH + 1 }>,
    block_counter: u64,
}

impl HasherWithTree {
    fn new_internal(key: &crate::CVWords, flags: u8) -> Self {
        Self {
            tree: Vec::new(),
            block_state: BlockState::new(*key, flags),
            cv_stack: ArrayVec::new(),
            block_counter: 0,
        }
    }

    pub fn new() -> Self {
        Self::new_internal(crate::IV, 0)
    }

    pub fn new_keyed(key: &[u8; crate::KEY_LEN]) -> Self {
        let key_words = platform::words_from_le_bytes_32(key);
        Self::new_internal(&key_words, crate::KEYED_HASH)
    }

    pub fn new_derive_key(context: &str) -> Self {
        let context_key = crate::hash_all_at_once::<join::SerialJoin>(
            context.as_bytes(),
            crate::IV,
            crate::DERIVE_KEY_CONTEXT,
        )
        .root_hash();
        let context_key_words = platform::words_from_le_bytes_32(context_key.as_bytes());
        Self::new_internal(&context_key_words, crate::DERIVE_KEY_MATERIAL)
    }

    pub fn update(&mut self, input: &[u8]) {
        self.update_with_join::<join::SerialJoin>(input);
    }

    pub fn update_with_join<J: join::Join>(&mut self, mut input: &[u8]) {
        // If we have an incomplete block, try to feed it more bytes.
        let block_state_len = self.block_state.len();
        if block_state_len > 0 {
            let want = URSA_BLOCK_SIZE_BYTES - block_state_len;
            let take = cmp::min(want, input.len());
            self.block_state.update::<J>(&input[..take]);
            input = &input[take..];

            if input.is_empty() {
                return;
            }

            // The block is filled, let's finalize it and push it to the stack.
            let block_cv = self.block_state.final_output().chaining_value();
            self.push_cv(&block_cv);
            self.block_state.move_to_next_block();

            debug_assert_eq!(
                self.block_state.chunk_state.len(),
                0,
                "chunk state must be empty"
            );
        }

        while input.len() >= 2 * URSA_BLOCK_SIZE_BYTES {
            // If the caller of this function keeps passing chunks of exact size of the Ursa block
            // size, we will only ever reach this loop in the code which is super fast.
            let cv_pair = crate::compress_subtree_to_parent_node::<J>(
                &input[..2 * URSA_BLOCK_SIZE_BYTES],
                &self.block_state.key,
                self.block_state.chunk_state.chunk_counter,
                self.block_state.chunk_state.flags,
                self.block_state.chunk_state.platform,
            );

            let left_cv = array_ref!(cv_pair, 0, 32);
            let right_cv = array_ref!(cv_pair, 32, 32);
            self.push_cv(left_cv);
            self.push_cv(right_cv);

            self.block_state.chunk_state.chunk_counter += 2 * URSA_BLOCK_SIZE_IN_CHUNK as u64;
            input = &input[2 * URSA_BLOCK_SIZE_BYTES..];
        }

        // If we are hashing any block other than the first one (i.e cv_stack.len() > 0), we
        // already know we don't need to use that block as a root_hash, so we can compress it
        // here.
        let is_non_first_block = !self.cv_stack.is_empty() && input.len() == URSA_BLOCK_SIZE_BYTES;
        // If we have a complete block with an additional byte, we know we can finalize it here.
        let input_larger_than_one_block = input.len() > URSA_BLOCK_SIZE_BYTES;

        if input_larger_than_one_block || is_non_first_block {
            let cv_pair = crate::compress_subtree_to_parent_node::<J>(
                &input[..URSA_BLOCK_SIZE_BYTES],
                &self.block_state.key,
                self.block_state.chunk_state.chunk_counter,
                self.block_state.chunk_state.flags,
                self.block_state.chunk_state.platform,
            );

            let left_cv = array_ref!(cv_pair, 0, 32);
            let right_cv = array_ref!(cv_pair, 32, 32);
            let parent_output = crate::parent_node_output(
                &left_cv,
                &right_cv,
                &self.block_state.key,
                self.block_state.chunk_state.flags,
                self.block_state.chunk_state.platform,
            )
            .chaining_value();

            self.push_cv(&parent_output);
            self.block_state.chunk_state.chunk_counter += URSA_BLOCK_SIZE_IN_CHUNK as u64;
            input = &input[URSA_BLOCK_SIZE_BYTES..];
        }

        debug_assert!(input.len() <= URSA_BLOCK_SIZE_BYTES);
        if !input.is_empty() {
            self.merge_cv_stack();
            self.block_state.update::<J>(input);
        }
    }

    #[inline(always)]
    fn merge_cv_stack(&mut self) {
        let post_merge_stack_len = self.block_counter.count_ones() as usize;
        while self.cv_stack.len() > post_merge_stack_len {
            let right_child = self.cv_stack.pop().unwrap();
            let left_child = self.cv_stack.pop().unwrap();
            let parent_cv = crate::parent_node_output(
                &left_child,
                &right_child,
                &self.block_state.key,
                self.block_state.chunk_state.flags,
                self.block_state.chunk_state.platform,
            )
            .chaining_value();
            self.cv_stack.push(parent_cv);
            self.tree.push(parent_cv);
        }
    }

    fn push_cv(&mut self, new_cv: &crate::CVBytes) {
        self.merge_cv_stack();
        self.cv_stack.push(*new_cv);
        self.tree.push(*new_cv);
        self.block_counter += 1;
    }

    fn final_output(&mut self) -> crate::Output {
        // If the current chunk is the only chunk, that makes it the root node
        // also. Convert it directly into an Output. Otherwise, we need to
        // merge subtrees below.
        if self.cv_stack.is_empty() {
            return self.block_state.final_output();
        }

        let mut output: crate::Output;
        let mut num_cvs_remaining = self.cv_stack.len();

        if self.block_state.len() > 0 {
            debug_assert_eq!(
                self.cv_stack.len(),
                self.block_counter.count_ones() as usize,
                "cv stack does not need a merge"
            );
            output = self.block_state.final_output();
        } else {
            debug_assert!(self.cv_stack.len() >= 2);
            output = crate::parent_node_output(
                &self.cv_stack[num_cvs_remaining - 2],
                &self.cv_stack[num_cvs_remaining - 1],
                &self.block_state.key,
                self.block_state.chunk_state.flags,
                self.block_state.chunk_state.platform,
            );
            num_cvs_remaining -= 2;
        }
        while num_cvs_remaining > 0 {
            self.tree.push(output.chaining_value());
            output = crate::parent_node_output(
                &self.cv_stack[num_cvs_remaining - 1],
                &output.chaining_value(),
                &self.block_state.key,
                self.block_state.chunk_state.flags,
                self.block_state.chunk_state.platform,
            );
            num_cvs_remaining -= 1;
        }
        output
    }

    pub fn finalize(mut self) -> WithTreeHashOutput {
        let root_hash = self.final_output().root_hash();
        self.tree.push(root_hash.0.clone());
        WithTreeHashOutput {
            hash: root_hash,
            tree: self.tree,
        }
    }
}

pub struct WithTreeHashOutput {
    pub hash: crate::Hash,
    pub tree: Vec<[u8; 32]>,
}

/// Incremental hasher for a single block, this can only be used to hash only one block.
pub struct BlockState {
    key: crate::CVWords,
    chunk_state: crate::ChunkState,
    cv_stack: ArrayVec<crate::CVBytes, { URSA_BLOCK_SIZE_IN_CHUNK_LOG_2 + 1 }>,
}

impl BlockState {
    pub fn new(key: crate::CVWords, flags: u8) -> Self {
        Self {
            key,
            chunk_state: crate::ChunkState::new(&key, 0, flags, platform::Platform::detect()),
            cv_stack: ArrayVec::new(),
        }
    }

    /// Make this block state ready for the next block, clears the stack and moves the
    /// chunk_counter by one.
    #[inline(always)]
    pub fn move_to_next_block(&mut self) {
        self.cv_stack.clear();
        self.chunk_state = crate::ChunkState::new(
            &self.key,
            self.chunk_state.chunk_counter + 1,
            self.chunk_state.flags,
            self.chunk_state.platform,
        );

        self.chunk_state.chunk_counter -=
            self.chunk_state.chunk_counter & URSA_BLOCK_SIZE_IN_CHUNK_MOD_MASK;
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        let mut chunk_counter =
            (self.chunk_state.chunk_counter & URSA_BLOCK_SIZE_IN_CHUNK_MOD_MASK) as usize;

        if chunk_counter == 0 && self.cv_stack.len() > 0 {
            chunk_counter = URSA_BLOCK_SIZE_IN_CHUNK;
        }

        chunk_counter * crate::CHUNK_LEN + self.chunk_state.len()
    }

    #[inline(always)]
    pub fn update<J: join::Join>(&mut self, mut input: &[u8]) {
        debug_assert!(
            input.len() + self.len() <= URSA_BLOCK_SIZE_BYTES,
            "data for HalfBlockState exceeded its limit."
        );

        if self.chunk_state.len() > 0 {
            let want = crate::CHUNK_LEN - self.chunk_state.len();
            let take = cmp::min(want, input.len());
            self.chunk_state.update(&input[..take]);
            input = &input[take..];

            if input.is_empty() {
                return;
            }

            debug_assert_eq!(self.chunk_state.len(), crate::CHUNK_LEN);

            // There is more data coming in, which means this is not the root so we can
            // finalize the chunk state here and move the chunk counter forward.
            let chunk_cv = self.chunk_state.output().chaining_value();
            self.push_cv(&chunk_cv, self.chunk_state.chunk_counter);

            // Reset the chunk state and move the chunk_counter forward.
            self.chunk_state = crate::ChunkState::new(
                &self.key,
                self.chunk_state.chunk_counter + 1,
                self.chunk_state.flags,
                self.chunk_state.platform,
            );

            // Chunk state is complete. Move on with reading the full chunks.
        }

        while input.len() > crate::CHUNK_LEN {
            debug_assert_eq!(self.chunk_state.len(), 0, "no partial chunk data");
            debug_assert_eq!(crate::CHUNK_LEN.count_ones(), 1, "power of 2 chunk len");
            let mut subtree_len = crate::largest_power_of_two_leq(input.len());
            let count_so_far = self.chunk_state.chunk_counter * crate::CHUNK_LEN as u64;
            // Shrink the subtree_len until it evenly divides the count so far.
            // We know that subtree_len itself is a power of 2, so we can use a
            // bitmasking trick instead of an actual remainder operation. (Note
            // that if the caller consistently passes power-of-2 inputs of the
            // same size, as is hopefully typical, this loop condition will
            // always fail, and subtree_len will always be the full length of
            // the input.)
            //
            // An aside: We don't have to shrink subtree_len quite this much.
            // For example, if count_so_far is 1, we could pass 2 chunks to
            // compress_subtree_to_parent_node. Since we'll get 2 CVs back,
            // we'll still get the right answer in the end, and we might get to
            // use 2-way SIMD parallelism. The problem with this optimization,
            // is that it gets us stuck always hashing 2 chunks. The total
            // number of chunks will remain odd, and we'll never graduate to
            // higher degrees of parallelism. See
            // https://github.com/BLAKE3-team/BLAKE3/issues/69.
            while (subtree_len - 1) as u64 & count_so_far != 0 {
                subtree_len /= 2;
            }
            // The shrunken subtree_len might now be 1 chunk long. If so, hash
            // that one chunk by itself. Otherwise, compress the subtree into a
            // pair of CVs.
            let subtree_chunks = (subtree_len / crate::CHUNK_LEN) as u64;
            if subtree_len <= crate::CHUNK_LEN {
                debug_assert_eq!(subtree_len, crate::CHUNK_LEN);
                self.push_cv(
                    &crate::ChunkState::new(
                        &self.key,
                        self.chunk_state.chunk_counter,
                        self.chunk_state.flags,
                        self.chunk_state.platform,
                    )
                    .update(&input[..subtree_len])
                    .output()
                    .chaining_value(),
                    self.chunk_state.chunk_counter,
                );
            } else {
                // This is the high-performance happy path, though getting here
                // depends on the caller giving us a long enough input.
                let cv_pair = crate::compress_subtree_to_parent_node::<J>(
                    &input[..subtree_len],
                    &self.key,
                    self.chunk_state.chunk_counter,
                    self.chunk_state.flags,
                    self.chunk_state.platform,
                );
                let left_cv = array_ref!(cv_pair, 0, 32);
                let right_cv = array_ref!(cv_pair, 32, 32);
                // Push the two CVs we received into the CV stack in order. Because
                // the stack merges lazily, this guarantees we aren't merging the
                // root.
                self.push_cv(left_cv, self.chunk_state.chunk_counter);
                self.push_cv(
                    right_cv,
                    self.chunk_state.chunk_counter + (subtree_chunks / 2),
                );
            }
            self.chunk_state.chunk_counter += subtree_chunks;
            input = &input[subtree_len..];
        }

        // What remains is 1 chunk or less. Add it to the chunk state.
        debug_assert!(input.len() <= crate::CHUNK_LEN);
        if !input.is_empty() {
            self.chunk_state.update(input);
        }
    }

    #[inline(always)]
    fn merge_cv_stack(&mut self, total_len: u64) {
        // Here we diverge from the default incremental hasher implementation,
        // the `& URSA_BLOCK_SIZE_IN_CHUNK_MASK` is basically `% URSA_BLOCK_SIZE_IN_CHUNK`,
        // and we do this because the stack of the previous blocks are not going to be part
        // of the block state.
        // Because of that at the beginning of every block, we basically reset the counter,
        // hence resetting the expected number of items already in the stack to zero as well.
        let post_merge_stack_len =
            (total_len & URSA_BLOCK_SIZE_IN_CHUNK_MOD_MASK).count_ones() as usize;
        while self.cv_stack.len() > post_merge_stack_len {
            let right_child = self.cv_stack.pop().unwrap();
            let left_child = self.cv_stack.pop().unwrap();
            let parent_output = crate::parent_node_output(
                &left_child,
                &right_child,
                &self.key,
                self.chunk_state.flags,
                self.chunk_state.platform,
            );
            self.cv_stack.push(parent_output.chaining_value());
        }
    }

    fn push_cv(&mut self, new_cv: &crate::CVBytes, chunk_counter: u64) {
        self.merge_cv_stack(chunk_counter);
        self.cv_stack.push(*new_cv);
    }

    fn final_output(&self) -> crate::Output {
        // If the current chunk is the only chunk, that makes it the root node
        // also. Convert it directly into an Output. Otherwise, we need to
        // merge subtrees below.
        if self.cv_stack.is_empty() {
            return self.chunk_state.output();
        }

        // If there are any bytes in the ChunkState, finalize that chunk and
        // merge its CV with everything in the CV stack. In that case, the work
        // we did at the end of update() above guarantees that the stack
        // doesn't contain any unmerged subtrees that need to be merged first.
        // (This is important, because if there were two chunk hashes sitting
        // on top of the stack, they would need to merge with each other, and
        // merging a new chunk hash into them would be incorrect.)
        //
        // If there are no bytes in the ChunkState, we'll merge what's already
        // in the stack. In this case it's fine if there are unmerged chunks on
        // top, because we'll merge them with each other. Note that the case of
        // the empty chunk is taken care of above.
        let mut output: crate::Output;
        let mut num_cvs_remaining = self.cv_stack.len();
        if self.chunk_state.len() > 0 {
            debug_assert_eq!(
                self.cv_stack.len(),
                (self.chunk_state.chunk_counter & URSA_BLOCK_SIZE_IN_CHUNK_MOD_MASK).count_ones()
                    as usize,
                "cv stack does not need a merge"
            );
            output = self.chunk_state.output();
        } else {
            debug_assert!(self.cv_stack.len() >= 2);
            output = crate::parent_node_output(
                &self.cv_stack[num_cvs_remaining - 2],
                &self.cv_stack[num_cvs_remaining - 1],
                &self.key,
                self.chunk_state.flags,
                self.chunk_state.platform,
            );
            num_cvs_remaining -= 2;
        }
        while num_cvs_remaining > 0 {
            output = crate::parent_node_output(
                &self.cv_stack[num_cvs_remaining - 1],
                &output.chaining_value(),
                &self.key,
                self.chunk_state.flags,
                self.chunk_state.platform,
            );
            num_cvs_remaining -= 1;
        }
        output
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::platform;

    /// The seed for our LCG randomness used for the testing.
    const LCG_SEED: [u8; 4] = [11, 13, 17, 19];

    /// A very unsafe but efficient PRNG for the purpose of testing the hash.
    #[inline(always)]
    fn lcg(state: [u8; 4]) -> [u8; 4] {
        (u32::from_be_bytes(state).wrapping_mul(48271) % 0x7fffffff).to_be_bytes()
    }

    /// Fill a buffer with random bytes.
    fn fill(mut state: [u8; 4], buffer: &mut [u8]) -> [u8; 4] {
        for block in buffer.chunks_mut(4) {
            state = lcg(state);
            for i in 0..block.len() {
                block[i] = state[i];
            }
        }
        state
    }

    struct Tester {
        hasher: crate::Hasher,
        ursa: HasherWithTree,
        bytes: usize,
    }

    impl Tester {
        pub fn new() -> Self {
            Self {
                hasher: crate::Hasher::new_derive_key("ursa-test"),
                ursa: HasherWithTree::new_derive_key("ursa-test"),
                bytes: 0,
            }
        }

        pub fn write(&mut self, input: &[u8]) {
            self.hasher.update(input);
            self.ursa.update(input);
            self.bytes += input.len();
            assert_eq!(
                self.ursa.block_state.chunk_state.chunk_counter,
                self.hasher.chunk_state.chunk_counter
            );
        }

        pub fn test(self) {
            let num_blocks = (self.bytes + URSA_BLOCK_SIZE_BYTES - 1) / URSA_BLOCK_SIZE_BYTES;
            let expected_tree_size = (2 * num_blocks).saturating_sub(1).max(1);
            let hash = self.hasher.finalize();
            let result = self.ursa.finalize();
            assert_eq!(result.tree.len(), expected_tree_size);
            assert_eq!(hash, result.hash);
            assert_eq!(result.tree[result.tree.len() - 1], hash.0);
        }
    }

    #[test]
    fn block_state_against_reference() {
        let mut block_state = BlockState::new(*crate::IV, 0);
        let mut hasher = crate::Hasher::new();
        for i in 0..URSA_BLOCK_SIZE_BYTES {
            block_state.update::<join::SerialJoin>(&[i as u8]);
            hasher.update(&[i as u8]);
        }
        let expected = hasher.final_output().chaining_value();
        let actual = block_state.final_output().chaining_value();
        assert_eq!(actual, expected);
    }

    #[test]
    fn block_state_2_block_root_hash() {
        let mut hasher = crate::Hasher::new();

        let c1 = {
            let mut block_state = BlockState::new(*crate::IV, 0);
            for i in 0..URSA_BLOCK_SIZE_BYTES {
                let b = ((i + 17) % 256) as u8;
                block_state.update::<join::SerialJoin>(&[b]);
                hasher.update(&[b]);
            }
            block_state.final_output().chaining_value()
        };

        let c2 = {
            let mut block_state = BlockState::new(*crate::IV, 0);
            block_state.chunk_state.chunk_counter = URSA_BLOCK_SIZE_IN_CHUNK as u64;

            for i in 0..URSA_BLOCK_SIZE_BYTES {
                let b = ((i + 5) % 256) as u8;
                block_state.update::<join::SerialJoin>(&[b]);
                hasher.update(&[b]);
            }

            block_state.final_output().chaining_value()
        };

        let expected = hasher.final_output().root_hash();
        let actual =
            crate::parent_node_output(&c1, &c2, crate::IV, 0, platform::Platform::detect())
                .root_hash();

        assert_eq!(actual, expected);
    }

    fn block_state_3rd_block_write_by(chunk_size: usize) {
        // Create some random looking data.
        let mut data = [0; URSA_BLOCK_SIZE_BYTES];
        for i in 0..URSA_BLOCK_SIZE_BYTES {
            data[i] = i as u8;
        }

        // Hash the data as the 3rd block by writing it byte by byte.
        let mut block_state = BlockState::new(*crate::IV, 0);
        block_state.chunk_state.chunk_counter = 2 * URSA_BLOCK_SIZE_IN_CHUNK as u64;
        for chunk in data.chunks(chunk_size) {
            block_state.update::<join::SerialJoin>(chunk);
        }
        let actual = block_state.final_output().chaining_value();

        // Compute the same result using the trusted code.
        let cv_pair = crate::compress_subtree_to_parent_node::<join::SerialJoin>(
            &data,
            crate::IV,
            2 * URSA_BLOCK_SIZE_IN_CHUNK as u64,
            0,
            platform::Platform::detect(),
        );

        // Generate the root chaining value by merging the parent pair.
        let left_cv = array_ref!(cv_pair, 0, 32);
        let right_cv = array_ref!(cv_pair, 32, 32);
        let expected = crate::parent_node_output(
            &left_cv,
            &right_cv,
            crate::IV,
            0,
            platform::Platform::detect(),
        )
        .chaining_value();

        assert_eq!(actual, expected);
    }

    #[test]
    fn block_state_3rd_block_byte_by_byte() {
        block_state_3rd_block_write_by(1);
        block_state_3rd_block_write_by(2);
        block_state_3rd_block_write_by(64);
        block_state_3rd_block_write_by(65);
    }

    #[test]
    fn block_state_3rd_block_by_chunks() {
        for i in 1..=URSA_BLOCK_SIZE_IN_CHUNK {
            block_state_3rd_block_write_by(i * crate::CHUNK_LEN);
            block_state_3rd_block_write_by(i * crate::CHUNK_LEN + 1);
            block_state_3rd_block_write_by(i * crate::CHUNK_LEN - 1);
        }
    }

    #[test]
    fn empty_hash() {
        let tester = Tester::new();
        tester.test();
    }

    #[test]
    fn one_byte() {
        let mut tester = Tester::new();
        tester.write(&[0]);
        tester.test();

        let mut tester = Tester::new();
        tester.write(&[17]);
        tester.test();
    }

    #[test]
    fn one_byte_one_chunk() {
        let mut tester = Tester::new();
        tester.write(&[3]);
        let mut chunk = [0; crate::CHUNK_LEN];
        fill(LCG_SEED, &mut chunk);
        tester.write(&chunk);
        tester.test();
    }

    #[test]
    fn one_chunk_one_byte() {
        let mut tester = Tester::new();
        let mut chunk = [0; crate::CHUNK_LEN];
        fill(LCG_SEED, &mut chunk);
        tester.write(&chunk);
        tester.write(&[3]);
        tester.test();
    }

    #[test]
    fn one_chunk() {
        let mut tester = Tester::new();
        let mut chunk = [0; crate::CHUNK_LEN];
        fill(LCG_SEED, &mut chunk);
        tester.write(&chunk);
        tester.test();
    }

    #[test]
    fn one_block() {
        let mut tester = Tester::new();
        let mut chunk = [0; URSA_BLOCK_SIZE_BYTES];
        fill(LCG_SEED, &mut chunk);
        tester.write(&chunk);
        tester.test();
    }

    #[test]
    fn two_block() {
        let mut tester = Tester::new();
        let mut chunk = [0; 2 * URSA_BLOCK_SIZE_BYTES];
        fill(LCG_SEED, &mut chunk);
        tester.write(&chunk);
        tester.test();
    }

    #[test]
    fn three_block() {
        let mut tester = Tester::new();
        let mut chunk = [0; 3 * URSA_BLOCK_SIZE_BYTES];
        fill(LCG_SEED, &mut chunk);
        tester.write(&chunk);
        tester.test();
    }

    #[test]
    fn four_block() {
        let mut tester = Tester::new();
        let mut chunk = [0; 4 * URSA_BLOCK_SIZE_BYTES];
        fill(LCG_SEED, &mut chunk);
        tester.write(&chunk);
        tester.test();
    }

    #[test]
    fn two_block_byte_by_byte() {
        let mut tester = Tester::new();
        let mut block = [0; 2 * URSA_BLOCK_SIZE_BYTES];
        fill(LCG_SEED, &mut block);

        for byte in block.chunks(1) {
            tester.write(byte);
        }

        tester.test();
    }

    #[test]
    fn one_block_byte_by_byte() {
        let mut tester = Tester::new();
        let mut block = [0; 2 * URSA_BLOCK_SIZE_BYTES];
        fill(LCG_SEED, &mut block);

        for byte in block.chunks(1) {
            tester.write(byte);
        }

        tester.test();
    }

    #[test]
    fn two_block_one_byte() {
        let mut tester = Tester::new();
        let mut block = [0; 2 * URSA_BLOCK_SIZE_BYTES];
        fill(LCG_SEED, &mut block);
        tester.write(&block);
        tester.write(&[0]);
        tester.test();
    }

    #[test]
    fn four_block_by_byte() {
        let mut tester = Tester::new();
        let mut block = [0; 2 * URSA_BLOCK_SIZE_BYTES];
        fill(LCG_SEED, &mut block);
        for byte in block.chunks(1) {
            tester.write(byte);
        }
        tester.write(&[0]);
        tester.test();
    }

    #[test]
    fn two_block_by_half_block() {
        let mut tester = Tester::new();
        let mut block = [0; 2 * URSA_BLOCK_SIZE_BYTES];
        fill(LCG_SEED, &mut block);

        for byte in block.chunks(URSA_BLOCK_SIZE_BYTES / 2) {
            tester.write(byte);
        }

        tester.test();
    }

    #[test]
    fn two_block_by_half_block_irregular() {
        let mut tester = Tester::new();
        let mut block = [0; 2 * URSA_BLOCK_SIZE_BYTES];
        fill(LCG_SEED, &mut block);
        for (i, byte) in block.chunks(URSA_BLOCK_SIZE_BYTES / 2).enumerate() {
            tester.write(byte);
            if i % 17 == 0 {
                tester.write(&[0]);
            }

            if i % 11 == 0 {
                tester.write(&[1, 2]);
            }
        }
        tester.test();
    }

    #[test]
    fn fuzz() {
        let mut state = LCG_SEED;

        for mut n in 0..(1 << 12) {
            let mut tester = Tester::new();
            for _ in 0..4 {
                // Get the data for this round.
                let mut data = [0; 2 * URSA_BLOCK_SIZE_BYTES];
                state = fill(state, &mut data);

                // Get the write mode.
                let test = n & 7;
                n >>= 3;

                match test {
                    // Skip
                    0 => {}
                    // By byte
                    1 => {
                        for byte in data.chunks(1) {
                            tester.write(byte);
                        }
                    }
                    // By chunk
                    2 => {
                        for byte in data.chunks(crate::CHUNK_LEN) {
                            tester.write(byte);
                        }
                    }
                    // By 1/2 block
                    3 => {
                        for byte in data.chunks(URSA_BLOCK_SIZE_BYTES / 2) {
                            tester.write(byte);
                        }
                    }
                    // By block
                    4 => {
                        for byte in data.chunks(URSA_BLOCK_SIZE_BYTES) {
                            tester.write(byte);
                        }
                    }
                    // By 2 block (full)
                    5 => {
                        for byte in data.chunks(2 * URSA_BLOCK_SIZE_BYTES) {
                            tester.write(byte);
                        }
                    }
                    // Trailing byte
                    6 => {
                        for byte in data.chunks(2 * URSA_BLOCK_SIZE_BYTES) {
                            tester.write(byte);
                        }
                        tester.write(&[0x00]);
                    }
                    // Leading byte
                    7 => {
                        tester.write(&[0x00]);
                        for byte in data.chunks(2 * URSA_BLOCK_SIZE_BYTES) {
                            tester.write(byte);
                        }
                    }
                    _ => unreachable!(),
                }
            }
            tester.test();
        }
    }
}
