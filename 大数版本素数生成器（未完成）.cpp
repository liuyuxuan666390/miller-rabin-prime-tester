#include <stdio.h>
#include <stdlib.h>
#include <time.h>

/*
 * 1024-bit prime generator using Miller-Rabin test
 * - Only uses stdio, stdlib, time (as required)
 * - Implements big integer arithmetic (1024-bit)
 * - Uses small-prime trial division for quick filtering
 * - Generates random 1024-bit prime
 * - Saves generated prime in hex to "prime1024.txt"
 */

/* 1024-bit number represented as array of 32-bit words */
/* 1024 bits = 32 words of 32 bits */
#define WORDS_COUNT 32
typedef struct {
    unsigned int words[WORDS_COUNT];
} bigint1024;

/* Small primes for quick filtering */
static const unsigned int small_primes[] = {
    2,3,5,7,11,13,17,19,23,29,
    31,37,41,43,47,53,59,61,67,71,
    73,79,83,89,97,101,103,107,109,113,
    127,131,137,139,149,151,157,163,167,173,
    179,181,191,193,197,199
};
static const int small_primes_count = 46;

/* Utility functions */
static void bigint_zero(bigint1024 *a) {
    int i;
    for (i = 0; i < WORDS_COUNT; i++) {
        a->words[i] = 0;
    }
}

static void bigint_set_u32(bigint1024 *a, unsigned int val) {
    bigint_zero(a);
    a->words[0] = val;
}

static int bigint_is_zero(const bigint1024 *a) {
    int i;
    for (i = 0; i < WORDS_COUNT; i++) {
        if (a->words[i] != 0) return 0;
    }
    return 1;
}

static int bigint_is_one(const bigint1024 *a) {
    int i;
    if (a->words[0] != 1) return 0;
    for (i = 1; i < WORDS_COUNT; i++) {
        if (a->words[i] != 0) return 0;
    }
    return 1;
}

static int bigint_is_even(const bigint1024 *a) {
    return (a->words[0] & 1) == 0;
}

static void bigint_copy(bigint1024 *dst, const bigint1024 *src) {
    int i;
    for (i = 0; i < WORDS_COUNT; i++) {
        dst->words[i] = src->words[i];
    }
}

/* Compare two big integers: return 1 if a > b, 0 if a == b, -1 if a < b */
static int bigint_compare(const bigint1024 *a, const bigint1024 *b) {
    int i;
    for (i = WORDS_COUNT - 1; i >= 0; i--) {
        if (a->words[i] > b->words[i]) return 1;
        if (a->words[i] < b->words[i]) return -1;
    }
    return 0;
}

/* Generate random 1024-bit number */
static void bigint_rand(bigint1024 *a) {
    int i;
    for (i = 0; i < WORDS_COUNT; i++) {
        /* Generate 32-bit random value */
        a->words[i] = ((unsigned int)rand() << 16) ^ (unsigned int)rand();
    }
}

/* Generate random 1024-bit odd number with high bit set */
static void bigint_rand_odd_1024(bigint1024 *a) {
    bigint_rand(a);
    /* Set highest bit to ensure it's 1024 bits */
    a->words[WORDS_COUNT-1] |= 0x80000000U;
    /* Make it odd */
    a->words[0] |= 1;
}

/* Left shift by 1 bit */
static void bigint_shl_one(bigint1024 *a) {
    unsigned int carry = 0;
    int i;
    for (i = 0; i < WORDS_COUNT; i++) {
        unsigned int next_carry = a->words[i] >> 31;
        a->words[i] = (a->words[i] << 1) | carry;
        carry = next_carry;
    }
}

/* Right shift by 1 bit */
static void bigint_shr_one(bigint1024 *a) {
    unsigned int carry = 0;
    int i;
    for (i = WORDS_COUNT - 1; i >= 0; i--) {
        unsigned int next_carry = a->words[i] & 1;
        a->words[i] = (a->words[i] >> 1) | (carry << 31);
        carry = next_carry;
    }
}

/* Add two big integers: c = a + b, returns carry */
static unsigned int bigint_add(bigint1024 *c, const bigint1024 *a, const bigint1024 *b) {
    unsigned long long sum = 0;
    int i;
    for (i = 0; i < WORDS_COUNT; i++) {
        sum = sum + (unsigned long long)a->words[i] + (unsigned long long)b->words[i];
        c->words[i] = (unsigned int)sum;
        sum = sum >> 32;
    }
    return (unsigned int)sum;
}

/* Subtract: c = a - b, assumes a >= b */
static void bigint_sub(bigint1024 *c, const bigint1024 *a, const bigint1024 *b) {
    unsigned long long borrow = 0;
    int i;
    for (i = 0; i < WORDS_COUNT; i++) {
        unsigned long long diff = (unsigned long long)a->words[i] - (unsigned long long)b->words[i] - borrow;
        c->words[i] = (unsigned int)diff;
        borrow = (diff >> 32) & 1;
    }
}

/* Helper: check if a >= b */
static int bigint_gte(const bigint1024 *a, const bigint1024 *b) {
    return bigint_compare(a, b) >= 0;
}

/* Multiply: c = a * b (simple schoolbook multiplication) */
static void bigint_mul(bigint1024 *c, const bigint1024 *a, const bigint1024 *b) {
    bigint_zero(c);
    unsigned long long temp[WORDS_COUNT * 2] = {0};
    int i, j;
    
    for (i = 0; i < WORDS_COUNT; i++) {
        unsigned long long carry = 0;
        for (j = 0; j < WORDS_COUNT; j++) {
            unsigned long long product = (unsigned long long)a->words[i] * (unsigned long long)b->words[j] + temp[i+j] + carry;
            temp[i+j] = product & 0xFFFFFFFFULL;
            carry = product >> 32;
        }
        if (i + WORDS_COUNT < WORDS_COUNT * 2) {
            temp[i + WORDS_COUNT] = carry;
        }
    }
    
    /* Copy result to c (only lower 1024 bits) */
    for (i = 0; i < WORDS_COUNT; i++) {
        c->words[i] = (unsigned int)temp[i];
    }
}

/* Modular multiplication: c = (a * b) mod n */
static void bigint_mod_mul(bigint1024 *c, const bigint1024 *a, const bigint1024 *b, const bigint1024 *n) {
    /* Simple implementation: multiply then reduce */
    bigint1024 prod;
    bigint_mul(&prod, a, b);
    
    /* Reduce modulo n using repeated subtraction */
    bigint1024 rem, n_shifted, two;
    bigint_copy(&rem, &prod);
    bigint_copy(&n_shifted, n);
    
    /* Find shift count to align n with rem */
    int shift = 0;
    bigint_set_u32(&two, 2);
    
    while (bigint_compare(&n_shifted, &rem) < 0) {
        bigint_shl_one(&n_shifted);
        shift++;
    }
    
    /* Repeated subtraction */
    while (shift >= 0) {
        if (bigint_compare(&rem, &n_shifted) >= 0) {
            bigint_sub(&rem, &rem, &n_shifted);
        }
        bigint_shr_one(&n_shifted);
        shift--;
    }
    
    bigint_copy(c, &rem);
}

/* Modular exponentiation: c = (base^exp) mod mod */
static void bigint_mod_exp(bigint1024 *c, const bigint1024 *base, const bigint1024 *exp, const bigint1024 *mod) {
    bigint1024 result, b, e;
    bigint_set_u32(&result, 1);
    bigint_copy(&b, base);
    bigint_copy(&e, exp);
    
    while (!bigint_is_zero(&e)) {
        if (e.words[0] & 1) {
            bigint_mod_mul(&result, &result, &b, mod);
        }
        bigint_mod_mul(&b, &b, &b, mod);
        bigint_shr_one(&e);
    }
    
    bigint_copy(c, &result);
}

/* Check if a is divisible by small prime p */
static int bigint_divisible_by_small_prime(const bigint1024 *a, unsigned int p) {
    /* Compute a mod p using Horner's method */
    unsigned long long rem = 0;
    int i;
    for (i = WORDS_COUNT - 1; i >= 0; i--) {
        rem = ((rem << 32) | a->words[i]) % p;
    }
    return rem == 0;
}

/* Miller-Rabin witness test */
static int miller_rabin_witness_1024(const bigint1024 *n, const bigint1024 *a) {
    /* Check if a >= n */
    if (bigint_compare(a, n) >= 0) {
        bigint1024 temp;
        bigint_copy(&temp, a);
        while (bigint_compare(&temp, n) >= 0) {
            bigint_sub(&temp, &temp, n);
        }
        if (bigint_is_zero(&temp)) return 1;
        bigint_copy((bigint1024*)a, &temp); /* Use the reduced value */
    }
    
    /* Write n-1 = d * 2^s */
    bigint1024 d, n_minus_1;
    bigint_copy(&n_minus_1, n);
    bigint1024 one;
    bigint_set_u32(&one, 1);
    bigint_sub(&n_minus_1, n, &one);
    bigint_copy(&d, &n_minus_1);
    
    int s = 0;
    while (bigint_is_even(&d)) {
        bigint_shr_one(&d);
        s++;
    }
    
    /* Compute x = a^d mod n */
    bigint1024 x;
    bigint_mod_exp(&x, a, &d, n);
    
    if (bigint_is_one(&x) || bigint_compare(&x, &n_minus_1) == 0) {
        return 1;
    }
    
    int r;
    for (r = 1; r < s; r++) {
        bigint_mod_mul(&x, &x, &x, n);
        if (bigint_compare(&x, &n_minus_1) == 0) {
            return 1;
        }
    }
    
    return 0;
}

/* Generate random a in [2, n-2] */
static void bigint_rand_range(bigint1024 *a, const bigint1024 *n) {
    bigint1024 n_minus_3;
    bigint_copy(&n_minus_3, n);
    bigint1024 three;
    bigint_set_u32(&three, 3);
    bigint_sub(&n_minus_3, n, &three);
    
    /* Generate random number */
    bigint_rand(a);
    
    /* Reduce modulo (n-3) */
    bigint1024 temp;
    bigint_copy(&temp, a);
    while (bigint_compare(&temp, &n_minus_3) >= 0) {
        bigint_sub(&temp, &temp, &n_minus_3);
    }
    
    /* Add 2 to get range [2, n-2] */
    bigint1024 two;
    bigint_set_u32(&two, 2);
    bigint_add(a, &temp, &two);
}

/* Check if number is probably prime using Miller-Rabin */
static int is_probable_prime_1024(const bigint1024 *n, int rounds) {
    int i;
    
    /* Small prime check */
    for (i = 0; i < small_primes_count; i++) {
        if (bigint_divisible_by_small_prime(n, small_primes[i])) {
            /* Check if n equals the small prime */
            bigint1024 p_val;
            bigint_set_u32(&p_val, small_primes[i]);
            if (bigint_compare(n, &p_val) == 0) {
                return 1;
            }
            return 0;
        }
    }
    
    /* Miller-Rabin test with random bases */
    bigint1024 a;
    for (i = 0; i < rounds; i++) {
        /* Generate random a in [2, n-2] */
        bigint_rand_range(&a, n);
        
        if (!miller_rabin_witness_1024(n, &a)) {
            return 0;
        }
    }
    
    return 1;
}

/* Convert bigint to hex string */
static void bigint_to_hex(const bigint1024 *a, char *buf, int buf_size) {
    int i;
    int pos = 0;
    int leading_zero = 1;
    
    for (i = WORDS_COUNT - 1; i >= 0; i--) {
        if (leading_zero && a->words[i] == 0) {
            continue;
        }
        
        if (leading_zero) {
            pos += snprintf(buf + pos, buf_size - pos, "%x", a->words[i]);
            leading_zero = 0;
        } else {
            pos += snprintf(buf + pos, buf_size - pos, "%08x", a->words[i]);
        }
    }
    
    if (leading_zero) {
        snprintf(buf, buf_size, "0");
    }
}

/* Display progress */
static void display_progress(int attempts, time_t start_time) {
    double elapsed = difftime(time(NULL), start_time);
    printf("\rAttempts: %d, Time: %.1f seconds", attempts, elapsed);
    fflush(stdout);
}

/* Generate 1024-bit prime within time limit (2 minutes) */
static void generate_1024bit_prime(void) {
    time_t start_time = time(NULL);
    time_t time_limit = 120; /* 2 minutes */
    int attempts = 0;
    int rounds = 10; /* Miller-Rabin rounds */
    
    printf("Generating 1024-bit prime ...\n");
    
    while (1) {
        attempts++;
 
        /* Display progress every 100 attempts */
        if (attempts % 100 == 0) {
            display_progress(attempts, start_time);
        }
        
        /* Generate random odd 1024-bit number */
        bigint1024 candidate;
        bigint_rand_odd_1024(&candidate);
        
        /* Quick divisibility test with small primes */
        int divisible = 0;
        int i;
        for (i = 0; i < small_primes_count; i++) {
            if (bigint_divisible_by_small_prime(&candidate, small_primes[i])) {
                divisible = 1;
                break;
            }
        }
        
        if (divisible) {
            continue;
        }
        
        /* Miller-Rabin primality test */
        if (is_probable_prime_1024(&candidate, rounds)) {
            time_t end_time = time(NULL);
            double elapsed = difftime(end_time, start_time);
            
            printf("\n\nFound probable 1024-bit prime after %d attempts in %.1f seconds\n", 
                   attempts, elapsed);
            
            /* Convert to hex and display */
            char hex_buf[1024];
            bigint_to_hex(&candidate, hex_buf, sizeof(hex_buf));
            printf("Prime (hex): 0x%s\n", hex_buf);
            
            /* Count bits */
            int bit_count = 0;
            for (i = 0; hex_buf[i] != '\0'; i++) {
                char c = hex_buf[i];
                if (c >= '0' && c <= '9') bit_count += 4;
                else if (c >= 'a' && c <= 'f') bit_count += 4;
                else if (c >= 'A' && c <= 'F') bit_count += 4;
            }
            printf("Bit length: %d bits\n", bit_count);
            
            /* Save to file */
            FILE *f = fopen("prime1024.txt", "w");
            if (f != NULL) {
                fprintf(f, "0x%s\n", hex_buf);
                fclose(f);
                printf("Saved prime in hex to prime1024.txt\n");
            } else {
                printf("Failed to open prime1024.txt for writing\n");
            }
            
            return;
        }
        
        /* Reseed occasionally to avoid getting stuck */
        if (attempts % 1000 == 0) {
            srand((unsigned)time(NULL) + attempts);
        }
    }
}

int main() {
    srand((unsigned)time(NULL));
    
    printf("=============================================\n");
    printf("   1024-bit Prime Generator (Miller-Rabin)   \n");
    printf("=============================================\n\n");
    
    generate_1024bit_prime();
    
    printf("\nDone.\n");
    return 0;
}