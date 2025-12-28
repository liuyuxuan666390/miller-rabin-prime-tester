#include <stdio.h>
#include <stdlib.h>
#include <time.h>

/*
 * Miller-Rabin primality test implementation in C99
 * - Only uses stdio, stdlib, time
 * - Uses small-prime trial division for quick filtering
 * - For primality test picks 10 random bases, prints them (hex) and results
 * - Generates a random prime of specified bit length (default 30 bits)
 * - Saves generated prime in hex to "prime.txt"
 */

typedef unsigned long long ull;
typedef unsigned long ul;

/* Small primes for quick filtering */
static const int small_primes[] = {
    2,3,5,7,11,13,17,19,23,29,
    31,37,41,43,47,53,59,61,67,71,
    73,79,83,89,97,101,103,107,109,113,
    127,131,137,139,149,151,157,163,167,173,
    179,181,191,193,197,199
};
static const int small_primes_count = sizeof(small_primes)/sizeof(small_primes[0]);

/* Generate a 32-bit random value using rand() (portable) */
static unsigned int rand32(void) {
    unsigned int r = ((unsigned int)rand() & 0xFFFF);
    r = (r << 16) | ((unsigned int)rand() & 0xFFFF);
    return r;
}

/* Generate a random unsigned long long in [0, max) */
static ull rand_ull(ull max) {
    if (max == 0) return 0;
    ull r = 0;
    /* build 64-bit from multiple rand32 calls */
    r = ((ull)rand32() << 32) | (ull)rand32();
    return r % max;
}

/* Multiplication modulo without overflow: (a * b) % mod */
static ull mulmod(ull a, ull b, ull mod) {
    ull res = 0;
    a %= mod;
    while (b) {
        if (b & 1) {
            res += a;
            if (res >= mod) res -= mod;
        }
        a <<= 1;
        if (a >= mod) a -= mod;
        b >>= 1;
    }
    return res % mod;
}

/* Modular exponentiation: (base^exp) % mod */
static ull powmod(ull base, ull exp, ull mod) {
    ull res = 1;
    base %= mod;
    while (exp) {
        if (exp & 1) res = mulmod(res, base, mod);
        base = mulmod(base, base, mod);
        exp >>= 1;
    }
    return res;
}

/* Miller-Rabin witness test for base 'a'. Returns 1 if passes (likely prime for this base), 0 if composite */
static int miller_rabin_witness(ull n, ull a) {
    if (a % n == 0) return 1;
    ull d = n - 1;
    int s = 0;
    while ((d & 1) == 0) {
        d >>= 1;
        s++;
    }
    ull x = powmod(a, d, n);
    if (x == 1 || x == n - 1) return 1;
    for (int r = 1; r < s; ++r) {
        x = mulmod(x, x, n);
        if (x == n - 1) return 1;
    }
    return 0;
}

/* Perform k rounds with random bases, print bases (hex) and results. Returns 1 if probably prime. */
static int is_probable_prime_with_print(ull n, int k) {
    if (n < 2) return 0;
    /* small prime check */
    for (int i = 0; i < small_primes_count; ++i) {
        int p = small_primes[i];
        if ((ull)p == n) return 1;
        if (n % p == 0) return 0;
    }

    int all_pass = 1;
    for (int i = 0; i < k; ++i) {
        ull a;
        if (n > 4) a = 2 + rand_ull(n - 3);
        else a = 2;
        int pass = miller_rabin_witness(n, a);
        printf("  base %2d: 0x%llx -> %s\n", i+1, (unsigned long long)a, pass ? "probably prime" : "composite");
        if (!pass) all_pass = 0;
    }
    return all_pass;
}

/* Perform k rounds without printing (used for generation). Returns 1 if probably prime. */
static int is_probable_prime(ull n, int k) {
    if (n < 2) return 0;
    for (int i = 0; i < small_primes_count; ++i) {
        int p = small_primes[i];
        if ((ull)p == n) return 1;
        if (n % p == 0) return 0;
    }
    for (int i = 0; i < k; ++i) {
        ull a = 2 + rand_ull(n - 3);
        if (!miller_rabin_witness(n, a)) return 0;
    }
    return 1;
}

/* Generate a random odd number with given bit length (bits >= 2) */
static ull gen_random_odd(int bits) {
    if (bits < 2) return 3;
    /* generate value in [2^(bits-1) .. 2^bits -1] and make it odd */
    ull high = 1ULL << (bits - 1);
    ull range = (1ULL << bits) - high; /* range = 2^(bits-1) */
    ull r = rand_ull(range) + high;
    r |= 1ULL; /* make odd */
    return r;
}

/* Check primality for user-supplied hex input and print 10 bases and results */
static void check_input_hex(void) {
    char buf[256];
    printf("Enter number in hex (e.g. 0x1f,0x3b0c1abd): ");
    if (!fgets(buf, sizeof(buf), stdin)) return;
    /* parse hex, allow 0x prefix */
    char *endptr;
    ull n = strtoull(buf, &endptr, 0); /* base 0 allows 0x */
    printf("Testing input n = 0x%llx\n", (unsigned long long)n);
    /* small prime check */
    for (int i = 0; i < small_primes_count; ++i) {
        int p = small_primes[i];
        if ((ull)p == n) {
            printf("Number equals small prime %d -> prime\n", p);
            return;
        }
        if (n % p == 0) {
            printf("Divisible by small prime %d -> composite\n", p);
            return;
        }
    }
    int result = is_probable_prime_with_print(n, 10);
    if (result) printf("Overall result: probably prime\n");
    else printf("Overall result: composite\n");
}

/* Generate a 30-bit prime, display and save to file */
static void generate_30bit_prime(void) {
    int bits = 30;
    time_t start = time(NULL);
    int attempts = 0;
    ull candidate;
    while (1) {
        attempts++;
        candidate = gen_random_odd(bits);
        int divisible = 0;
        for (int i = 0; i < small_primes_count; ++i) {
            int p = small_primes[i];
            if ((ull)p == candidate) { divisible = 0; break; }
            if (candidate % p == 0) { divisible = 1; break; }
        }
        if (divisible) continue;
        if (is_probable_prime(candidate, 10)) break;
        if (difftime(time(NULL), start) > 60.0) {
            srand((unsigned)time(NULL) + attempts);
        }
    }
    time_t end = time(NULL);
    printf("\nFound probable %d-bit prime after %d attempts in %.0f seconds:\n", bits, attempts, difftime(end, start));
    printf("  p = 0x%llx\n", (unsigned long long)candidate);

    FILE *f = NULL;
#ifdef _MSC_VER
    if (fopen_s(&f, "prime.txt", "w") == 0 && f != NULL) {
#else
    f = fopen("prime.txt", "w");
    if (f != NULL) {
#endif
        fprintf(f, "0x%llx\n", (unsigned long long)candidate);
        fclose(f);
        printf("Saved prime in hex to prime.txt\n");
    } else {
        printf("Failed to open prime.txt for writing.\n");
    }
}

int main() {
    srand((unsigned)time(NULL));

    while (1) {
    	printf("\n -------------------------------------------------------------");
        printf("\n| Select option:                                              |\n");
        printf("|   1) Test a number (hex input) for primality                |\n");
        printf("|   2) Generate a random 30-bit prime and save to prime.txt   |\n");
        printf("|   3) Exit                                                   |\n");
        printf(" -------------------------------------------------------------\n");
        printf("Enter choice: ");
        int c = getchar();
        while (getchar() != '\n' && !feof(stdin));
        if (c == '1') {
            check_input_hex();
        } else if (c == '2') {
            generate_30bit_prime();
        } else if (c == '3') {
            break;
        } else {
            printf("Invalid choice\n");
        }
    }
    return 0;
}
