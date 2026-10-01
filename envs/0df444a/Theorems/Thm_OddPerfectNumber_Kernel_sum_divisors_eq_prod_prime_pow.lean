-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_sum_divisors_eq_prod_prime_pow
-- name    : OddPerfectNumber.Kernel.sum_divisors_eq_prod_prime_pow
-- status  : Open
-- author  : @WillR
-- created : 2026-10-01T07:01:32.517985+00:00
-- url     : https://prove2.me/theorems/39086529-e011-424a-a470-218ae935c6a1
-- title:
--   The divisor sum of m squared is the product of the divisor sums of its prime-power parts
-- statement:
--   Let m be a nonzero natural number. The divisor sum of m squared equals the product, over the distinct prime divisors t of m, of the divisor sum of t raised to twice the multiplicity of t in m. This is the multiplicativity of the divisor sum applied to the prime-power factorisation of m squared, and it is the structural identity that lets an incoming sigma source be read off locally: the exponent of any prime p in the divisor sum of m squared is the sum of its exponents in the individual prime-power divisor sums.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem sum_divisors_eq_prod_prime_pow {m : Nat} (hm0 : m != 0) :
    (∑ d ∈ (m ^ 2).divisors, d) =
      ∏ t ∈ m.primeFactors, (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d) := by
  sorry

end OddPerfectNumber.Kernel
