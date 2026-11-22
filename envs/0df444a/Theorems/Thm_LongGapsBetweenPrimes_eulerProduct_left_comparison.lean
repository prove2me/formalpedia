-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_eulerProduct_left_comparison
-- name    : LongGapsBetweenPrimes.eulerProduct_left_comparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:22.572474+00:00
-- url     : https://prove2.me/theorems/309fe523-deac-4d97-94f5-25c6f0bdcf6c
-- title:
--   Long Gaps Between Primes: euler Product left comparison
-- statement:
--   Bound the cost of shifting the Euler product to exponent `1 - t`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3733-L3749
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3733-L3749

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.eulerProduct_left_comparison (N : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    eulerProduct N (1 - t) ≤ eulerProduct N 1 *
      Real.exp (smoothEulerConstant * ∑ p ∈ N.primesLE, ((p : ℝ) ^ t - 1) / p) := by sorry
