-- Prove2me | Theorems.Thm_OddGoldbach19_primeCounting_second_order
-- name    : OddGoldbach19.primeCounting_second_order
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T16:19:56.948219+00:00
-- url     : https://prove2.me/theorems/eae0a770-521f-48c2-933c-21576c16a338
-- title:
--   A positive second-order lower bound for prime counting
-- statement:
--   For each natural number n with natural logarithm at least100, the number of primes at most n is at least n/log(n)+0.46*n/log(n)^2. The coefficient0.46 and logarithmic threshold100 are explicit constants derived from the existing Rosser–Schoenfeld theta estimate and partial summation. This is a prime-counting estimate, not a complete prime-sum campaign endpoint.
-- source:
--   Derived from Rosser–Schoenfeld (1962) Theorem4 eq(3.14), proved platform theorem TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic https://prove2.me/theorems/d4cf496a-eed1-4284-8d5d-f9cfbfb07786 ; Mathlib Chebyshev.primeCounting_eq_theta_div_log_add_integral. Constants0.46 and100 derived here, not quoted from the source.

import Mathlib

theorem OddGoldbach19.primeCounting_second_order (n : ℕ) (hl : 100 ≤ Real.log (n : ℝ)) :
    (n : ℝ) / Real.log n + 0.46 * n / (Real.log n) ^ 2 ≤ (Nat.primeCounting n : ℝ) := by sorry
