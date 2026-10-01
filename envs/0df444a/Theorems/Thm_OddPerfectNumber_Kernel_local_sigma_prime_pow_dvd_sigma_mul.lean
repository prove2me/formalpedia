-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_local_sigma_prime_pow_dvd_sigma_mul
-- name    : OddPerfectNumber.Kernel.local_sigma_prime_pow_dvd_sigma_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T17:56:15.56169+00:00
-- url     : https://prove2.me/theorems/7db1bbb5-fc9e-4edb-82db-069e9fae9135
-- title:
--   A local divisor sum at a prime dividing the base divides the whole divisor sum
-- statement:
--   Let n be a positive natural number and let t be a prime dividing n with factorization exponent e at least one. Then the local divisor sum of t to the power e, namely the sum of the first e plus one powers of t, divides the divisor sum of n. This is the multiplicativity of the divisor sum over prime powers, isolated at one prime factor.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem local_sigma_prime_pow_dvd_sigma_mul {n t : Nat} (hn : n != 0) (ht : t.Prime)
    (htd : Dvd.dvd t n) (he : 1 ≤ (n).factorization t) :
    Dvd.dvd (∑ i ∈ Finset.range ((n).factorization t + 1), t ^ i) (∑ d ∈ (n).divisors, d) := by
  sorry

end OddPerfectNumber.Kernel
