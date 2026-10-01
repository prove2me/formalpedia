-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_fermat_prime_dvd_geom_sum_odd_of_even_pow_h
-- name    : OddPerfectNumber.Kernel.fermat_prime_dvd_geom_sum_odd_of_even_pow_h
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-30T16:23:15.303969+00:00
-- url     : https://prove2.me/theorems/5dd24eed-336c-4208-b51e-2524a17bee45
-- title:
--   For a prime p with p-1 a power of two, a zero geometric sum of odd length forces p to divide the length
-- statement:
--   Let p be a prime whose predecessor p-1 is a power of two, and let t be a natural number not divisible by p. If p divides the geometric sum 1 + t + t^2 + ... + t^(2e) of odd length 2e+1, then p divides 2e+1. If t is congruent to 1 modulo p the sum is congruent to 2e+1, so p divides the length. Otherwise the multiplicative order of t modulo p divides the odd number 2e+1 and is therefore odd, but a cyclic group of order a power of two has no nontrivial element of odd order, a contradiction. This is the order-theoretic obstruction behind the k=5 second-Dris-equation residual: the demand that the p-adic valuation of sigma(m^2) be at least 5 cannot be met unless some prime factor of m occurs to an exponent e with p dividing 2e+1.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem fermat_prime_dvd_geom_sum_odd_of_even_pow_h (p t e : Nat) (hp : p.Prime)
    (ht0 : Not (Dvd.dvd t p)) (hpm1 : ∃ k, p - 1 = 2 ^ k)
    (hdvd : Dvd.dvd (∑ i ∈ Finset.range (2 * e + 1), t ^ i) p) :
    Dvd.dvd (2 * e + 1) p := by
  sorry

end OddPerfectNumber.Kernel
