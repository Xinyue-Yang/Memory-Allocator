/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * TODO: insert your documentation here. :)
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Xinyue Yang <xinyueya@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printf(...) ((void)printf(__VA_ARGS__))
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, these should emit no code whatsoever,
 * not even from evaluation of argument expressions.  However,
 * argument expressions should still be syntax-checked and should
 * count as uses of any variables involved.  This used to use a
 * straightforward hack involving sizeof(), but that can sometimes
 * provoke warnings about misuse of sizeof().  I _hope_ that this
 * newer, less straightforward hack will be more robust.
 * Hat tip to Stack Overflow poster chqrlie (see
 * https://stackoverflow.com/questions/72647780).
 */
#define dbg_discard_expr_(...) ((void)((0) && printf(__VA_ARGS__)))
#define dbg_requires(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_assert(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_ensures(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_printf(...) dbg_discard_expr_(__VA_ARGS__)
#define dbg_printheap(...) ((void)((0) && print_heap(__VA_ARGS__)))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = 2 * dsize;

/**
 * @brief Default size for expanding the heap (bytes)
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/** @brief Mask the allocated bit from a header or footer */
static const word_t alloc_mask = 0x1;

/** @brief Mask the size from a header or footer */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the doubly linked list structure and payload of one free block in the heap */
/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    union {
        /** @brief if free, keeps record of prev free block and next free block */
        struct {
            struct block *pred;
            struct block *succ;
        };

        /** @brief if allocated, keeps record to the block payload. */
        char payload[0];
    };
} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

/**
 * @brief Arranging free blocks by their size
 * 0 ~ 2^4, 2^4+1 ~ 2^5, ... 2^15+1 ~ inf
 * In each linked list, it is arranged from small size to big size
 */
static const int list_length = 15;
block_t *segregated_list[15];

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - dsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == (char *)mem_heap_hi() - 7);
    block->header = pack(0, true);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * @pre Block is non-NULL and free. Size is positive.
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    block->header = pack(size, alloc);
    word_t *footerp = header_to_footer(block);
    *footerp = pack(size, alloc);
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return NULL;
    }

    return footer_to_header(footerp);
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

static int find_index(size_t size) {
    if (size <= 16) return 0;
    for (int i = 1; i < list_length; i++) {
        if ((1 << (i + 3)) < size && size <= (1 << (i + 4))) {
            return i;
        }
    }
    return list_length - 1;
}


/**
 * @brief Inserts a block to the start of the free list
 *
 * @param[in] block The block to be inserted to the free list
 * @return void
 * @pre The block is free, and not in free list
 * @post The block is in the free list
 */
static void insert_to_free_list(block_t *block) {
    dbg_requires(!get_alloc(block));
    
    int i = find_index(get_size(block));
    // if the free list is empty, the block is now the start of the list
    if (segregated_list[i] == NULL) {
        block->pred = NULL;
        block->succ = NULL;
        segregated_list[i] = block;
    } 
    
    // if the free list is non-empty, insert the block to the front
    else {
        block->pred = NULL;
        block->succ = segregated_list[i];
        segregated_list[i]->pred = block;
        segregated_list[i] = block;
    }
}

/**
 * @brief Removes a block from the free list
 *
 * @param[in] block The block to be removed from the free list
 * @return void
 * @pre The block is free
 */
static void remove_from_free_list(block_t *block) {
    block_t *prev_block = block->pred;
    block_t *next_block = block->succ;
    int i = find_index(get_size(block));

    // case 1: no prev & next block; the free list is now empty
    if (prev_block == NULL && next_block == NULL) {
        segregated_list[i] = NULL;
    }

    // case 2: no prev free block; next free block is now the first
    else if (prev_block == NULL) {
        next_block->pred = NULL;
        segregated_list[i] = next_block;
    }

    // case 3: no next free block; prev free block is now the last
    else if (next_block == NULL) {
        prev_block->succ = NULL;
    }

    // case 4: prev & next block exist
    else {
        next_block->pred = prev_block;
        prev_block->succ = next_block;
    }
}


/**
 * @brief Combines the previous and/or next blocks if they are free.
 *
 * @param[in] block A free block
 * @return Current block after coalescing
 * @pre The block is free and is in the free list.
 * @post The new block is still free and in the free list.
 */
static block_t *coalesce_block(block_t *block) {
    bool prev_alloc, next_alloc;
    // if the block is the first / last in the heap, can't coalesce
    if (find_prev(block) == NULL) {
        prev_alloc = true;
    } else {
        prev_alloc = get_alloc(find_prev(block));
    }
    
    if (find_next(block) == NULL) {
        next_alloc = true;
    } else {
        next_alloc = get_alloc(find_next(block));
    }

    size_t size = get_size(block);

    // case1: prev block and next block are allocated
    if (prev_alloc && next_alloc) {
        // dbg_assert(mm_checkheap(__LINE__));
        return block;
    }

    // case2: prev block is allocated; next block is free
    else if (prev_alloc && !next_alloc) {
        size += get_size(find_next(block));
        remove_from_free_list(find_next(block));
        write_block(block, size, false);

        // dbg_assert(mm_checkheap(__LINE__));
        return block;
    }

    // case3: prev block is free; next block is allocated
    else if (!prev_alloc && next_alloc) {
        size += get_size(find_prev(block));
        remove_from_free_list(find_prev(block));
        write_block(find_prev(block), size, false);
        
        // dbg_assert(mm_checkheap(__LINE__));
        return find_prev(block);
    }

    // case4: prev block and next block are free
    else {
        size += get_size(find_prev(block)) + get_size(find_next(block));
        remove_from_free_list(find_prev(block));
        remove_from_free_list(find_next(block));
        write_block(find_prev(block), size, false);
        
        // dbg_assert(mm_checkheap(__LINE__));
        return find_prev(block);
    }
}

/**
 * @brief Extends the heap with a new free block.
 *
 * @param[in] size The size of extension
 * @return The extended block
 * @pre The size is non-negative.
 * @post The new block is free.
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk((intptr_t)size)) == (void *)-1) {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false);
    //    insert_to_free_list(block);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);
    // ? insert
    insert_to_free_list(block);

    return block;
}

/**
 * @brief Splits an allocated block into one allocated block of the given size,
 *         and the remaining space is a free block.
 *
 * @param[in] block The block to be splitted
 * @param[in] asize The allocated size of the block
 * @return Void
 * @pre The requested size is no larger than the block size.
 * @post The block pointer remains the same.
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    /* TODO: Can you write a precondition about the value of asize? */
    dbg_requires(asize <= get_size(block));

    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        write_block(block, asize, true);

        block_next = find_next(block);
        write_block(block_next, block_size - asize, false);
        // ????
        insert_to_free_list(block_next);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief Find a free block large enough to hold the given size.
 *
 * @param[in] asize The requested size of the block
 * @return A free block, or NULL is not found
 * @pre The requested size is positive.
 * @post The returned block is free.
 */
static block_t *find_fit(size_t asize) {
    block_t *block;
    int i = find_index(asize);

    while (i < list_length) {
        /* return when we reached the end of segregated list / found a fit block */
        for (block = segregated_list[i]; block != NULL; block = block->succ) {

            if (asize <= get_size(block) && !get_alloc(block)) {
                return block;
            }
        }
        i++;
    }

    return NULL; // no fit found
}

/**
 * @brief check if prologue/epilogue is valid
 * @param[in] prologue, epilogue
 * @return true if they are good
 */
static bool check_prologue_epilogue(block_t *block) {
    if (!get_alloc(block)) {
        dbg_printf("prologue/epilogue allocated \n");
        return false;
    }
    if (get_size(block) != 0) {
        dbg_printf("prologue/epilogue has positive size \n");
        return false;
    }
    if ((size_t)block < (size_t)mem_heap_lo() || (size_t)block > (size_t)mem_heap_hi()) {
        dbg_printf("prologue/epilogue out of bound \n");
        return false;
    }

    return true;
}

/**
 * @brief Checks if the block is valid.
 *
 * @param[in] block The block to be checked
 * @return True if the block is valid; False otherwise
 */
static bool check_block(block_t *block) {
    word_t header = block->header;
    word_t footer = *header_to_footer(block);
    size_t size = get_size(block);
    bool alloc = get_alloc(block);
    block_t *prev_block = find_prev(block);
    block_t *next_block = find_next(block);

    // Check if the block is doubleword aligned
    if (get_size(block) % dsize != 0) {
        dbg_printf("%p is not doubleword aligned\n", (void*)block);
        return false;
    }

    // Check if the block has matched header and footer
    if (header != footer) {
        dbg_printf("%p has unmatched header and footer\n", (void*)block);
        return false;        
    }

    // Check if the block stores consistent sizes
    if (extract_size(header) != size || extract_size(footer) != size) {
        dbg_printf("%p stores unconsistent sizes\n", (void*)block);
        return false;          
    }

    // Check if the block stores consistent allocation status
    if (extract_alloc(header) != alloc || extract_alloc(footer) != alloc) {
        dbg_printf("%p stores unconsistent allocation status\n", (void*)block);
        return false;          
    }

    // Check no consecutive free blocks
    if (!alloc){
        if (prev_block != NULL && !get_alloc(prev_block)) {
            dbg_printf("%p has a consecitive free block before it\n", (void*)block);
            return false;   
        }
        if (next_block != NULL && !get_alloc(next_block)) {
            dbg_printf("%p has a consecitive free block after it\n", (void*)block);
            return false;   
        }
    }

    return true;
}

/**
 * @brief Checks if the block is valid.
 *
 * @param[in] block The block to be checked
 * @param[in] i index of the segregated list that the block belongs
 * @return True if the block is valid; False otherwise
 */
static bool check_free_block(block_t *block, int i) {
    bool alloc = get_alloc(block);
    size_t block_size = get_size(block);
    block_t *prev_block = block->pred;
    block_t *next_block = block->succ;

    // Check if the block is free
    if (alloc) {
        dbg_printf("%p is allocated but in the free list\n", (void*)block);
        return false;          
    }

    // Check if the free list pointer is inside the heap
    if ((char *)block < (char *)mem_heap_lo() || (char *)block > (char *)mem_heap_hi()) {
        dbg_printf("%p is outside the heap\n", (void*)block);
        return false;           
    }

    // Check if next/previous pointers are consistent
    if (prev_block != NULL && prev_block->succ != block) {
        dbg_printf("%p has inconsistent pred free blocks\n", (void*)block);
        return false;           
    }

    if (next_block != NULL && next_block->pred != block) {
        dbg_printf("%p has inconsistent succ free blocks\n", (void*)block);
        return false;          
    }

    // Check if the size is belong to the segregated list
    if (find_index(block_size) != i) {
        dbg_printf("%p belongs to the wrong segregated list\n", (void*)block);
        return false;          
    }

    return true;
}

/**
 * @brief Checks if the heap is valid.
 *
 * @param[in] line The line number
 * @return True if the heap is valid; False otherwise
 */
bool mm_checkheap(int line) {
    block_t *prologue = (block_t *)((word_t *)heap_start - 1);
    block_t *epilogue = (block_t *)((char *)mem_heap_hi() - 7);

    /* check prologue/epilogue */
    if (!check_prologue_epilogue(prologue)) {
        dbg_printf("prologue error\n");
        return false;
    }
    if (!check_prologue_epilogue(epilogue)) {
        dbg_printf("epilogue error\n");
        return false;
    }

    /* check block */
    block_t *start = heap_start;
    while (start != NULL && get_size(start) != 0) {
        if (!check_block(start)) {
            dbg_printf("Invalid block (called at line %d)\n", line);
            return false;
        }
        start = find_next(start);
    }

    // Check free list
    block_t *free_block;

    for (int i = 0; i < list_length; i++) {
        for (free_block = segregated_list[i]; free_block != NULL; free_block = free_block->succ) {
            if (!check_free_block(free_block, i)) {
                dbg_printf("Invalid free block (called at line %d)\n", line);
                return false;   
            }         
        }
    }

    return true;
}

static void print_heap() {
    block_t *prologue = (block_t *)((word_t *)heap_start - 1);
    block_t *epilogue = (block_t *)((char *)mem_heap_hi() - 7);
    dbg_printf("prologue at %p\n", (void *)prologue);

    block_t *start = heap_start;
    while (start != NULL && get_size(start) != 0) {
        dbg_printf("block at %p, size is %zu, payload is %zu, %d\n", (void *)start, get_size(start), get_payload_size(start), get_alloc(start));
        start = find_next(start);
    }

    dbg_printf("epilogue at %p\n\n", (void *)epilogue);
}

/**
 * @brief Initializes the heap structure.
 *
 * @return true if successful, false otherwise
 * @post The initialized heap is valid and empty. Heap_start points to the first block.
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    start[0] = pack(0, true); // Heap prologue (block footer)
    start[1] = pack(0, true); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    // Initialize segregated list
    for (int i = 0; i < list_length; i++) {
        segregated_list[i] = NULL;
    }

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    // print_heap();
    dbg_ensures(mm_checkheap(__LINE__));
    return true;
}

/**
 * @brief Allocate an uninitialized block of requested size
 *
 * @param[in] size The requested size to be allocated
 * @return a pointer to the allocated block of at least size bytes
 * @pre size > 0
 * @post The heap after the allocation is still valid
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        if (!(mm_init())) {
            dbg_printf("Problem initializing heap. Likely due to sbrk");
            return NULL;
        }
    }
    dbg_assert(mm_checkheap(__LINE__));

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    size_t block_size = get_size(block);
    write_block(block, block_size, true);
    // ??
    remove_from_free_list(block);

    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    // print_heap();
    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief Frees an allocated block
 *
 * @param[in] bp a pointer to the block payload
 * @return void
 * @pre bp is NULL or points to the beginning of a block payload
 * @post the corresponding block is freed
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false);

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);
    insert_to_free_list(block);

    // print_heap();
    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief Changes the size of a previously allocated block
 *
 * @param[in] ptr a pointer to the block payload
 * @param[in] size the new size to be allocated
 * @return the new block
 * @pre size >= 0
 * @post ptr is freed
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief Allocates memory for an elements-length array of size bytes each,
 *        initializes the memory to all bytes zero
 *
 * @param[in] elements number of elements to be allocate
 * @param[in] size the size of each element in the array
 * @return a pointer to the allocated memory
 * @pre size >= 0, elements >= 0
 * @post the allocated block is initialized to 0
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
