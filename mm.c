/*
 *mm.c
 *
 *Name: Zehao Chen
 *
 *In this iteration of the code, I used the free list approch mentioned in the text book.
 *where instead of iterating through the whole list and finindg the blocks that are free, 
 *I have an extra free list that is stored along side the block using pointers (prev_free)
 *and (next_free). This allow the program to look  up free blocks faster and assign them to the
 *corresponind sizes
 *
 *
 */


//always make sure to remove the list before setting the value, or the check will fail
#include <assert.h>
#include <stdlib.h>
#include <config.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"
#include "stree.h"
/*
 *If you want to enable your debugging outset_int_value and heap checker code, 
 *uncomment the following line. Be sure not to have debugging enabled
 *in your final submission.
 */
// #define DEBUG

#ifdef DEBUG
// When debugging is enabled, the underlying functions get called
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
// When debugging is disabled, no code gets generated
#define dbg_printf(...)
#define dbg_assert(...)
#endif // DEBUG

// do not change the following!
#ifdef DRIVER
// create aliases for driver tests
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mm_memset
#define memcpy mm_memcpy
#endif // DRIVER




#define ALIGNMENT 16
//bit mask and endmark
#define BLKSZMASK 0xf
#define ALLOCATED_MASK 0x1
#define ENDMARK (void *) 0x01// where the size is 0 and its allocat


// rounds up to the nearest multiple of ALIGNMENT
static size_t align(size_t x)
{
    return ALIGNMENT *((x+ALIGNMENT-1)/ALIGNMENT);
}
//basic size definition
#define WORD 4
#define DWORD 2*WORD 
//this is 8
//hyper tuning parameter
#define HEAP_SIZE DWORD*16
#define LIST_SIZE 500
//other stuff 
#define MIN_BLOCK_SIZE DWORD *4
#define HEADER_SZ DWORD
#define FOOTER_SZ DWORD

void *free_list[LIST_SIZE];
void *heapstart = NULL;


//static inline functions(bascially macros but safer)

static inline size_t ptr_to_num(void *ptr)
{
	return *(size_t *)(ptr);
}
static inline size_t alloc(void *ptr)
{
	return (size_t)(ptr_to_num(ptr) & ALLOCATED_MASK);
}

static inline void*combine(size_t val, size_t alloc)
{
	return (void*)((val) | (alloc));
}

static inline void set_l(void *ptr, void *value)
{ 
	*(size_t *)(ptr) = (size_t)(value);
}

static inline size_t blksz(void *ptr)
{
	return (size_t)(ptr_to_num(ptr) & ~BLKSZMASK);
}



static inline void *prev_free(void *ptr)
{
	return ptr;
}
static inline void *next_free(void *ptr)
{
    char*char_ptr = (char*) ptr;
	return char_ptr + DWORD;
}



static inline void *get_header(void *ptr)
{
    char*char_ptr = ptr;
	return (char_ptr) - HEADER_SZ;
}

static inline void *get_footer(void *ptr)
{
    char*char_ptr = (char*)ptr;
	return (char_ptr) + blksz(get_header(char_ptr)) - DWORD *2;
}



static inline void *prev_list(void *ptr)
{
    char**char_list_ptr = (char**) ptr;
    return *char_list_ptr;
}
static inline void *next_list(void *ptr)
{
    char**char_list_ptr = next_free(ptr);
	return *char_list_ptr;
}




static inline void *prev_blk(void*ptr) {
    char*char_ptr = (char*) ptr;
    return char_ptr-(blksz(char_ptr-DWORD*2));
}

static inline void *next_blk(void *ptr)
{
    char*char_ptr = (char*) ptr;
	return (char_ptr) + blksz(get_header(char_ptr));
}


static inline void set_value(void *ptr, size_t size, int allocation)
{
    set_l(get_header(ptr), combine(size, allocation));
    set_l(get_footer(ptr), combine(size, allocation));
}


/*
 *Return whether the pointer is in the heap.
 *May be useful for debugging.
 */
static bool in_heap(const void*p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 *Return whether the pointer is aligned.
 *May be useful for debugging.
 */
static bool aligned(const void*p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}






static int size_to_power(size_t x) {
    int power = 0;
    size_t size = 32;

    while (size < x) 
    {
        size *= 2;
        power++;
    }

    return power;
}





//func declaration 

static void insert_blk(void *ptr, size_t length);
static void remove_blk(void *ptr);
static void *extend_heap(size_t size);
static void *merge_block(void *ptr);
static void *split_block(void *curr_blk, size_t aligned_size);




static void insert_blk(void *blk, size_t length){

    int index = size_to_power(length);

    void *current_head_ptr = free_list[index]; 



    if (current_head_ptr != NULL)  
    { 
        free_list[index] = blk;
        set_l(prev_free(blk), NULL);
        set_l(prev_free(current_head_ptr), blk);        
        set_l(next_free(blk), current_head_ptr);
    }
    else 
    {
        free_list[index] = blk;
        set_l(prev_free(blk), NULL);
        set_l(next_free(blk), NULL);         
    }
}

static void remove_blk(void *blk){

	size_t length = blksz(get_header(blk));
	int index = size_to_power(length);
	
	if(prev_list(blk) != NULL)
    {

		if(next_list(blk) != NULL)
        {
			set_l(prev_free(next_list(blk)), prev_list(blk));
			set_l(next_free(prev_list(blk)), next_list(blk));
			
		}
		else
        {
			set_l(next_free(prev_list(blk)), NULL);
		}

	}
	else
    {
		if(next_list(blk) != NULL)
        {
            set_l(prev_free(next_list(blk)), NULL);
			free_list[index] = next_list(blk);
        }
		else
            free_list[index] = NULL;	
	}

}


static void *extend_heap(size_t size){

	size_t *new_block;	
	size_t aligned_size = align(size);


    new_block = mem_sbrk(aligned_size);//increase th heap
	
	if((size_t *) new_block == (void *) -1)
    // if they fail we fail too
		return NULL;
	
    //set the value and insert the new blk into the free list
    set_value(new_block, aligned_size, 0);

	insert_blk(new_block, aligned_size);	


    set_l(get_header(next_blk(new_block)), ENDMARK);	//set the end mark
	return new_block;
}




static void *merge_block(void *ptr){
	
    //get them blocks
	void *pr_block = prev_blk(ptr);
    void *nx_blk = next_blk(ptr);

    //get them allocations
    size_t prev_alloc = alloc(get_header(pr_block));
	size_t next_alloc = alloc(get_header(nx_blk));

    size_t size = blksz(get_header(ptr));

	if(!prev_alloc && !next_alloc)
    {
         //both are free
		
		remove_blk(pr_block);		
		remove_blk(nx_blk);

		size += blksz(get_footer(nx_blk));	
        size += blksz(get_header(pr_block));

        set_value(pr_block, size, 0);		
		ptr = pr_block;// we insert at the end so make sure we are refering to the right blk
		
	}	
    else if(!prev_alloc && next_alloc)
    {
        //prev is free
		remove_blk(pr_block);
        
		size += blksz(get_header(pr_block));

        set_value(pr_block, size, 0);	
		ptr = pr_block;
	}
	else if(prev_alloc && !next_alloc)
    {
        //next is free
		remove_blk(nx_blk);

		size += blksz(get_header(nx_blk));	

        set_value(ptr, size, 0);	
	}
    //if both are not free we just return 
	insert_blk(ptr, size);
	return ptr;
}





static void *split_block(void *curr_blk, size_t aligned_size){

	remove_blk(curr_blk);

    void *next_block;
	size_t og_size = blksz(get_header(curr_blk));
    size_t new_size = og_size - aligned_size;

	if((new_size) < (MIN_BLOCK_SIZE))
    {
        //not big enought to insert
        set_value(curr_blk, og_size, 1);
		if (!alloc(get_header(next_block)))
			set_l(get_footer(next_block), (void *)ptr_to_num(get_header(next_block)));		
	}
	else
    {
        //mark previous as occupied
        set_value(curr_blk, aligned_size, 1);

		next_block = next_blk(curr_blk);
        //set next as free and insert into the free list
        set_value(next_block, new_size, 0);
		insert_blk(next_block, new_size);
	}
	return curr_blk;
}




//-------------------------- official func implementation ------------------------------------------ 

/*
 *mm_init: returns false on error, true on success.
 */
bool mm_init(void)
{

	if((heapstart = mem_sbrk(MIN_BLOCK_SIZE)) == NULL)
    //fail to get space for the heap start
		return false;

	for(int i = 0; i < LIST_SIZE; i++)
    {
		free_list[i] = NULL;
	}

    //initialize the values 
	set_l(heapstart, 0);


	set_l(heapstart + DWORD, combine(2*HEADER_SZ, 1));
	set_l(heapstart + DWORD *2, combine(2*FOOTER_SZ, 1));

    set_l(heapstart + DWORD *3, ENDMARK); 

    heapstart += (DWORD *2);	

	if(extend_heap(HEAP_SIZE) ==  (void *)-1)
		return false;

	
	//mm_checkheap(1);

	return true;

}

void*find_best_fit(size_t aligned_size)
{
    int index = 0;
    void*best_fit = NULL;
        //finidng the best fit
	if((index = size_to_power(aligned_size) )!= LIST_SIZE)
    {
		best_fit = free_list[index];
			for(int i = 0; i < MIN_BLOCK_SIZE; i++)
            {
				if(best_fit == NULL)
					break;
				
				else if(aligned_size <= blksz(get_header(best_fit)))
                {
					split_block(best_fit, aligned_size);
					return best_fit;
				}
				best_fit = next_list(best_fit);
			}
	}

	index = index+1;
	best_fit = NULL;
	while((index < LIST_SIZE) && (best_fit == NULL))
    {
		best_fit = free_list[index];
		index++;
	}
    return best_fit;

}
/*
 *malloc
 */

void*malloc(size_t size)
{
	void *new_block = NULL;
	size_t aligned_size;
	size_t extend_size;

	if(size == 0)
		return NULL;
	
	else if((size>0)&&(size <= HEADER_SZ*2))
		aligned_size = MIN_BLOCK_SIZE;
	
	else if(size > HEADER_SZ*2)
		aligned_size = align(size + HEADER_SZ*2);
	

    new_block = find_best_fit(aligned_size);


	if(aligned_size >= LIST_SIZE)
		extend_size = aligned_size;
	else 
		extend_size = LIST_SIZE;

	if(new_block == NULL){
		new_block = extend_heap(extend_size);
	}
	split_block(new_block, aligned_size);
	
	//mm_checkheap(1);
  
	return new_block;
}
/*
 *free
 */
void free(void*ptr)
{
	size_t size;
	size = blksz(get_header(ptr));
    set_value(ptr, size, 0);;

	merge_block(ptr);
	
	//mm_checkheap(0);
    
}

/*
 *realloc
 */
void*realloc(void*ptr, size_t size)
{

	void *new_block = NULL;
	size_t realloc_size;
	size_t tmp_size;

    if(ptr == NULL)
    	return malloc(size);
    

    if(size == 0)
    {
    	free(ptr);
		return NULL;
    }

	
    new_block = malloc(size);
    tmp_size = blksz(get_header(ptr)) - HEADER_SZ;
    if(size <= tmp_size)
        realloc_size = size;
    else
        realloc_size = tmp_size;
    memcpy(new_block, ptr, realloc_size);
    free(ptr);
    


	//mm_checkheap(1);

	return new_block;

}

static bool in_free_list(void *ptr)
{
    void *free_block;

    // Iterate through all lists in the free list.
    for (int i = 0; i < LIST_SIZE; i++)
    {
        // Iterate through every block in the list.
        for (free_block = free_list[i]; free_block != NULL; free_block = next_list(free_block))
        {
            if (free_block == ptr)
                return true;
        }
    }
    
    // If we reach here, the block is not found in the free list.
    return false;
}




/*
 *mm_checkheap
 *You call the function via mm_checkheap(__LINE__)
 *The line number can be used to print the line number of the calling
 *function where there was an invalid heap.
 */
bool mm_checkheap(int line_number)
{
    void *ptr = heapstart;
    void *prev_block = NULL;
    while (blksz(get_header(ptr)) > 0) {
        // check alignment
        if (!aligned(ptr)) 
        {
            fprintf( stderr, "Error at line %d: %p is not aligned.\n", line_number, ptr);
            return false;
        }
        // check heap boundaries
        if (!in_heap(ptr)) 
        {
            fprintf( stderr, "Error at line %d: %p is not within heap boundaries.\n", line_number, ptr);
            return false;
        }

        // check contiguous free blocks
        if (prev_block && !alloc(get_header(prev_block)) && !alloc(get_header(ptr))) 
        {
            fprintf( stderr, "Error at line %d: %p and %p are contiguous free blocks.\n", line_number, prev_block, ptr);
            return false;
        }

        // check blocks in free list
        if (!alloc(get_header(ptr)) && !in_free_list(ptr)) 
        {
            fprintf( stderr, "Error at line %d: %p is a free block but not in free list.\n", line_number, ptr);
            return false;
        }

        prev_block = ptr;
        ptr = next_blk(ptr);
    }

    // check free list
    for (int i = 0; i < LIST_SIZE; i++) {
        for (ptr = free_list[i]; ptr != NULL; ptr = next_list(ptr)) 
        {
            // check heap boundaries
            if (!in_heap(ptr)) {
                fprintf( stderr, "Error at line %d: %p in free list is not within heap boundaries.\n", line_number, ptr);
                return false;
            }

            // check whether block is marked as free
            if (alloc(get_header(ptr))) {
                fprintf( stderr, "Error at line %d: %p in free list is marked as allocated.\n", line_number, ptr);
                return false;
            }
        }
    }

    return true;
}



/*
 *calloc
 *This function is not tested by mdriver, and has been implemented for you.
 */
void*calloc(size_t nmemb, size_t size)
{
    void*ret;
    size *= nmemb;
    ret = malloc(size);
    if (ret) {
        memset(ret, 0, size);
    }
    return ret;
}
