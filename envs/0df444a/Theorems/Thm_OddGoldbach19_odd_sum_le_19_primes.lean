-- Prove2me | Theorems.Thm_OddGoldbach19_odd_sum_le_19_primes
-- name    : OddGoldbach19.odd_sum_le_19_primes
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T20:54:13.7+00:00
-- url     : https://prove2.me/theorems/eae9b904-d94e-4f77-abbe-db087c0bd740
-- title:
--   Every Odd Number Greater Than1 is the Sum of at Most19 Primes
-- statement:
--   Every odd number greater than 1 is the sum of at most 19 primes, collected as a multiset (repetition allowed, order irrelevant).
-- source:
--   Known odd-integer corollary of the19-prime bound of H.Riesel and R.C.Vaughan, On sums of primes, Arkiv for Matematik21(1983), pp45-74, https://doi.org/10.1007/BF02384300 . This formal proof uses the finite-shift second moment and Schnirelmann-density method, with its own explicitly proved thresholds and kernel-checked finite arithmetic.

import Mathlib

theorem OddGoldbach19.odd_sum_le_19_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 19 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  sorry
