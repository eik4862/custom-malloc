/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc isn't implemented.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <limits.h>

#include "mm.h"
#include "memlib.h"

/**********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please  *
 * provide  your  information  in the  following  struct. *
 **********************************************************/
team_t team = {
    /* Your full name */
    "SangHyun Park",
    /* Your student ID */
    "2015-10283"
};

/* DON'T MODIFY THIS VALUE AND LEAVE IT AS IT WAS */
static range_t **gl_ranges;

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*
 * remove_range - manipulate range lists
 * DON'T MODIFY THIS FUNCTION AND LEAVE IT AS IT WAS
 */
static void remove_range(range_t **ranges, char *lo)
{
    range_t *p;
    range_t **prevpp = ranges;

    if (!ranges)
      return;

    for (p = *ranges;  p != NULL; p = p->next) {
      if (p->lo == lo) {
        *prevpp = p->next;
        free(p);
        break;
      }
      prevpp = &(p->next);
    }
}

/************************************** MACROS *************************************/
/* Constant */
#define WSIZE 4
#define DSIZE 8
#define ALOC 1
#define FREE 0
#define MEM_FAILURE -1
#define MEM_SUCCESS 0
#define BIN_CNT 13
#define MICRO_MEM_CNT 8
#define PROL_SIZE (BIN_CNT * 3 * WSIZE)
#define EPIL_SIZE (PROL_SIZE)
#define MICRO_MEM_SIZE (MICRO_MEM_CNT * WSIZE)

/* Getter */
#define GET_VAL(p) (*(size_t *)(p))
#define GET_SIZE(p) (GET_VAL(p) & ~0x7)
#define GET_ALOC(p) (GET_VAL(p) & 0x1)
#define GET_ADDR(p) (*(size_t **)(p))
#define READ_MICRO_MEM(idx) GET_VAL(micro_memp + (idx))

/* Setter */
#define SET_VAL(p, val) (*(size_t *)(p) = (val))
#define SET_HDR(p, size, alloc) (*(size_t *)(p) = ((size) | (alloc)))
#define SET_FTR(p, size, alloc) SET_HDR(p, size, alloc)
#define SET_PRE(p, addr) (*(size_t **)(p) = (addr))
#define SET_NXT(p, addr) SET_PRE(p, addr)
#define WRITE_MICRO_MEM(idx, size) SET_VAL(micro_memp + (idx), (size))

/* Access */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define PREP(bp) ((size_t **)(bp))
#define NXTP(bp) ((size_t **)((char *)(bp) + WSIZE))

/* Traverse */
#define NEXT_BLKP(bp) ((size_t *)((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))))
#define PREV_BLKP(bp) ((size_t *)((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))))
#define LAST_BLKP ((size_t *)((char *)segl_epilp - GET_SIZE((char *)segl_epilp - DSIZE)))
#define NEXT_BLKP_HDRP(bp) ((size_t *)((char *)(bp) + GET_SIZE(HDRP(bp)) - WSIZE))
#define PREV_BLKP_FTRP(bp) ((size_t *)((char *)(bp) - DSIZE))
#define NEXT_FREE_BLKP(bp) (GET_ADDR((char *)(bp) + WSIZE))
#define PREV_FREE_BLKP(bp) (GET_ADDR(bp))
#define FIRST_PROL_BLKP(idx) (segl_prolp + 3 * (idx))

/* ETC */
#define MAX(x, y) ((x > y) ? (x) : (y))
// __builtin_clzll for fast log2 computation
#define LOG2(x) ((size_t)(8 * sizeof(unsigned long long) - __builtin_clzll((x)) - 1))

/********************************** STATIC MEMBER **********************************/

static size_t *micro_memp;  // Pointer to the start of micro memory
static size_t *segl_prolp;  // Pointer to the start of segmented list prologue
static size_t *segl_epilp;  // Pointer to the start of segmented list epilogue
static size_t chunksize;    // Minimum chunk size for sbrk
static unsigned int cnt;    // Malloc counter
static char coal_flag;      // Flag for coalescing
static char empty_flag;     // Flag for empty heap

/************************************** HELPER *************************************/

void *extend_heap(size_t size);
size_t *coalesce(size_t *bp);
size_t *place(size_t *bp, size_t size);
void micro_sched(void);
size_t *segl_find(size_t size, unsigned int idx);
size_t *segl_push(size_t *bp);
size_t *segl_pop(size_t *bp);
size_t bin_idx(size_t size);

/**
 * extend_heap
 * Extend heap using mem_sbrk().
 * 
 * @arg size: Amount of extension. Must be multuple of DSIZE(8).
 * @return Pointer to the extended block
 **/
void *extend_heap(size_t size) {
    size_t *epil_old = segl_epilp;
    size_t *epil_new;
    size_t *bp;
    size_t *lbp;
    int i;
    char coal;

    // Selectively coalesce extended heap
    if (!empty_flag) {
        lbp = LAST_BLKP;
        
        // First, handle some marginal cases
        if (GET_ALOC(HDRP(lbp))) {
            size = MAX(size, chunksize);
            coal = 0;
        } else if (GET_VAL(PREV_BLKP_FTRP(lbp)) == 0) {
            size = size - GET_SIZE(HDRP(lbp));
            coal = 1;
        } else if (GET_SIZE(HDRP(PREV_BLKP(lbp))) < (size / 2)) {
            // If the last allocated block is small relatively, do not coalesce
            size = MAX(size, chunksize);
            coal = 0;
        } else {
            // If the last allocated block is large relativley, then coalesce
            size = size - GET_SIZE(HDRP(lbp));
            coal = 1;
        }
    } else {
        // If heap is empty, then it cannot coalesce
        size = MAX(size, chunksize);
        coal = 0;
    }

    // Extend heap
    if ((bp = (size_t *)mem_sbrk(size)) == NULL) return NULL;

    segl_epilp = (size_t *)((char *)bp + size - EPIL_SIZE + WSIZE);
    epil_new = segl_epilp;
    bp = epil_old;

    size_t *temp_prev_addr[BIN_CNT];
    size_t **temp_prev_nxtp_addr[BIN_CNT];

    // Move back segmented list epilogue
    for (i = 0; i < BIN_CNT; i++) {
        temp_prev_addr[i] = GET_ADDR(PREP(epil_old));
        temp_prev_nxtp_addr[i] = NXTP(PREV_FREE_BLKP(epil_old));
        epil_old += 3;
    }

    for (i = 0; i < BIN_CNT; i++) {
        SET_HDR(HDRP(epil_new), 0, ALOC);
        SET_PRE(PREP(epil_new), temp_prev_addr[i]);
        SET_NXT(temp_prev_nxtp_addr[i], epil_new);
        SET_NXT(NXTP(epil_new), NULL);
        epil_new += 3;
    }

    // Mark freash new block as free
    SET_HDR(HDRP(bp), size, FREE);
    SET_FTR(FTRP(bp), size, FREE);

    empty_flag = 0;

    // Coalesce if possible and return
    if (coal) bp = coalesce(bp);
    
    return bp;
}

/**
 * coalesce
 * Coalesce with adjacent free blocks if possible.
 * 
 * @arg bp: Pointer to the block to be coalesced.
 *          Must be already segl_popped from segmented list.
 * @return Pointer to the coalesed block
 **/
size_t *coalesce(size_t *bp) {
    // If coeal_flag is set to FALSE(0) then do not coalesce
    // This is for fast freeing at mm_exit
    if (!coal_flag) return bp;

    size_t palloc = GET_ALOC(PREV_BLKP_FTRP(bp));
    size_t nalloc = GET_ALOC(NEXT_BLKP_HDRP(bp));
    size_t size = GET_SIZE(HDRP(bp));

    if (palloc && nalloc) {
        // Case 1: neither previous nor next block is free
        return bp;
    }

    if (palloc && !nalloc) {
        // Case 2: only previous block is free
        segl_pop(NEXT_BLKP(bp));
        size += GET_SIZE(NEXT_BLKP_HDRP(bp));
        SET_HDR(HDRP(bp), size, FREE);
        SET_FTR(FTRP(bp), size, FREE);
    } else if (!palloc && nalloc) {
        // Case 3: only next block is free
        segl_pop(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        SET_FTR(FTRP(bp), size, FREE);
        SET_HDR(HDRP(PREV_BLKP(bp)), size, FREE);
        bp = PREV_BLKP(bp);
    } else {
        // Case 4: both previous and next block is free
        segl_pop(PREV_BLKP(bp));
        segl_pop(NEXT_BLKP(bp));
        size += GET_SIZE(NEXT_BLKP_HDRP(bp)) + GET_SIZE(HDRP(PREV_BLKP(bp)));
        SET_HDR(HDRP(PREV_BLKP(bp)), size, FREE);
        SET_FTR(FTRP(NEXT_BLKP(bp)), size, FREE);
        bp = PREV_BLKP(bp);
    }

    return bp;
}

/**
 * place
 * Fill in block info properly and split if needed.
 * 
 * @arg bp: Pointer to the block to be placed.
 *          Must be already segl_popped from its data structure.
 * @arg size: Size info to be filled. Must be multuple of DSIZE(8).
 * @return Pointer to the placed block
 **/
size_t *place(size_t *bp, size_t size) {
    size_t csize = GET_SIZE(HDRP(bp));
    size_t *split;

    if ((csize - size) < 2 * DSIZE) {
        // If current block size is not big enough, just place and return
        SET_HDR(HDRP(bp), csize, ALOC);
        SET_FTR(FTRP(bp), csize, ALOC);
    } else {
        // Otherwise, split
        SET_HDR(HDRP(bp), size, ALOC);
        SET_FTR(FTRP(bp), size, ALOC);
        split = NEXT_BLKP(bp);
        SET_HDR(HDRP(split), csize - size, FREE);
        SET_FTR(FTRP(split), csize - size, FREE);
        segl_push(split);
    }

    return bp;
}

/**
 * micro_sched
 * Estimate proper chunksize for memory util optimization.
 * chunksize for next 10 mallocs will be estimated by previous 10 malloc requests.
 * It is estimated as the second maximum previous 10 requests.
 **/
void micro_sched(void) {
    int i;
    size_t max = 0, second_max = 0;
    size_t temp;

    // Find second maximum
    for (i = 0; i < MICRO_MEM_CNT; i++) {
        temp = READ_MICRO_MEM(i);
        if (max < temp) {
            max = temp;
        } else if (second_max < temp) {
            second_max = temp;
        }
    }

    // Update chunksize
    chunksize = ALIGN(second_max);
}

/**
 * segl_find
 * Search best fit free block in segmented list bin $idx.
 * If search fail in bin $idx, then try next bin recursively.
 * Found block will be automatically popped from segmented list.
 * 
 * @arg size: Size to be allocated
 * @arg idx: Index of bin in segmented list
 * @return Pointer to the block found in segmented list. NULL if not found.
 **/
size_t *segl_find(size_t size, unsigned int idx) {
    // Search failed
    if (idx >= BIN_CNT) return NULL;
    
    size_t *find = NULL;
    size_t *bp;
    size_t min = UINT_MAX;

    // Loop all blocks in bin to find best fit
    for (bp = NEXT_FREE_BLKP(FIRST_PROL_BLKP(idx));
        GET_SIZE(HDRP(bp)) > 0; bp = NEXT_FREE_BLKP(bp)) {
        // If there is an exact fit, immediately return
        if ((GET_SIZE(HDRP(bp))) == size) return segl_pop(bp);

        // If there is block large enough, record it
        if ((GET_SIZE(HDRP(bp)) >= size) && (GET_SIZE(HDRP(bp)) < min)) {
            find = bp;
            min = GET_SIZE(HDRP(bp));
        }
    }

    // If there is at least one good fit, then return
    if (find != NULL) return segl_pop(find);

    // Otherwise, continue search at next level
    return segl_find(size, idx + 1);
}

/**
 * segl_push
 * Push free block $bp into the head of segmented list.
 * 
 * @arg bp: Pointer to the free block to be segl_pushed.
 *          Must be not a member of segmented list.
 * @return Pointer to the segl_pushed block
 **/
size_t *segl_push(size_t *bp) {
    size_t bin = bin_idx(GET_SIZE(HDRP(bp)));
    size_t *prev = FIRST_PROL_BLKP(bin);
    size_t *next = NEXT_FREE_BLKP(prev);

    // Relink previous and next blocks
    SET_NXT(NXTP(prev), bp);
    SET_PRE(PREP(next), bp);
    SET_NXT(NXTP(bp), next);
    SET_PRE(PREP(bp), prev);

    return bp;
}

/**
 * segl_pop
 * Pop block $bp from segmented list.
 * 
 * @arg bp: Pointer to the block to be segl_popped. Must be member of segmented list.
 * @return Pointer to the segl_popped block
 **/
size_t *segl_pop(size_t *bp) {
    SET_NXT(NXTP(PREV_FREE_BLKP(bp)), GET_ADDR(NXTP(bp)));
    SET_PRE(PREP(NEXT_FREE_BLKP(bp)), GET_ADDR(PREP(bp)));

    return bp;
}

/**
 * bin_idx
 * (Almost) macro for segmented list bin index computation.
 * Index is computed as log2($size) - 4.
 * 
 * @arg size: Size for index computation.
 * @return Index of proper index of segmented list bin
 **/
inline size_t bin_idx(size_t size) {
    size_t idx = LOG2(size) - 4;

    // Handle marginal cases
    if (idx < 0) return 0;
    if (idx >= BIN_CNT) return BIN_CNT - 1;

    return idx;
}

/********************************** MAIN PROCDURE **********************************/

int mm_init(range_t **ranges);
void *mm_malloc(size_t size);
void mm_free(void *ptr);

/**
 * mm_init
 * Initialize the malloc package
 * 
 * @arg ranges: ??
 * @return MM_SUCCESS(0) if success, MM_FAILURE(-1) otherwise
 **/
int mm_init(range_t **ranges) {
    size_t *bp;

    // Alloc prologue and epilogue blocks segmented list
    // Each bin in segmented list has own prologe and epilogue
    if ((bp = (size_t *)mem_sbrk(MICRO_MEM_SIZE + PROL_SIZE + EPIL_SIZE)) == NULL) {
        return MEM_FAILURE;
    }

    // Initialize static members
    micro_memp = bp;
    segl_prolp = (size_t *)((char *)bp + MICRO_MEM_SIZE);
    segl_epilp = (size_t *)((char *)segl_prolp + PROL_SIZE + WSIZE);
    chunksize = 0;
    cnt = 0;
    coal_flag = 1;
    empty_flag = 1;

    // Fill in epilogue and prologue blocks
    size_t *prolp = segl_prolp;
    size_t *epilp = segl_epilp;
    int i;

    bp = segl_prolp;

    for (i = 0; i < BIN_CNT; i++) {
        SET_PRE(PREP(bp), NULL);
        SET_NXT(NXTP(bp), epilp);
        // Cannot use FTRP(bp) since prologue block has no header
        SET_FTR(bp + 2, 0, ALOC);
        bp += 3;
        epilp += 3;
    }

    bp++;

    for (i = 0; i < BIN_CNT; i++) {
        SET_HDR(HDRP(bp), 0, ALOC);
        SET_PRE(PREP(bp), prolp);
        SET_NXT(NXTP(bp), NULL);
        bp += 3;
        prolp += 3;
    }

    /* DON'T MODIFY THIS STAGE AND LEAVE IT AS IT WAS */
    gl_ranges = ranges;

    return MEM_SUCCESS;
}

/**
 * mm_malloc
 * Find free block of $size and allocate.
 * First search for appropriate free block in segmented list.
 * If there is no room, then extend heap.
 * 
 * @arg size: Requested size for allocation
 * @return Pointer to the allocated block. NULL if allocation failed.
 **/
void *mm_malloc(size_t size) {
    if (size == 0) return NULL;

    size_t asize = ALIGN(size + DSIZE);
    size_t *bp;

    // Record 10 malloc requests and make estimation of chunksize for next 10 malloc
    if (cnt < MICRO_MEM_CNT) {
        WRITE_MICRO_MEM(cnt, asize);
        cnt++;
    } else {
        micro_sched();
        cnt = 0;
    }

    // If there is room for $size, find it and allocate
    if ((bp = segl_find(asize, bin_idx(asize))) != NULL) return place(bp, asize);

    // If there is no room, make it!
    if ((bp = extend_heap(asize)) != NULL) return place(bp, asize);

    return NULL;
}

/**
 * mm_free
 * Free block $bp and coalesce immediately if possible.
 * 
 * @arg ptr: Pointer to the block to be freed.
 **/
void mm_free(void *ptr) {
    // If one tries to double free abort
    if (!GET_ALOC(HDRP(ptr))) {
        printf("Double free\n");
        exit(EXIT_FAILURE);
    }

    size_t size = GET_SIZE(HDRP(ptr));

    SET_HDR(HDRP(ptr), size, FREE);
    SET_FTR(FTRP(ptr), size, FREE);
    segl_push(coalesce(ptr));

    /* DON'T MODIFY THIS STAGE AND LEAVE IT AS IT WAS */
    if (gl_ranges) remove_range(gl_ranges, ptr);
}

/**
 * mm_realloc
 * NOT IMPLEMENTED
 **/
void *mm_realloc(void *ptr, size_t t) {
    return NULL;
}

/**
 * mm_exit
 * Free all remaining free blocks
 **/
void mm_exit(void) {
    size_t *bp = (size_t *)((char *)segl_prolp + PROL_SIZE + WSIZE);

    // Set coal_flag to FALSE(0) for fast free
    coal_flag = 0;

    // Loop for all blocks in heap and free all allocated blocks
    for (bp = bp; bp != segl_epilp; bp = NEXT_BLKP(bp)) {
        if (GET_ALOC(HDRP(bp))) mm_free(bp);
    }
}
