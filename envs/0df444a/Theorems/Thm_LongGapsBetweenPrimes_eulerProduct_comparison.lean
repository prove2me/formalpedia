-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_eulerProduct_comparison
-- name    : LongGapsBetweenPrimes.eulerProduct_comparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:40.269114+00:00
-- url     : https://prove2.me/theorems/d4d8e60b-542b-430d-981e-6241db93a249
-- title:
--   Long Gaps Between Primes: euler Product comparison
-- statement:
--   Moving the Euler product to the right of its pole has bounded cost.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1077-L1096
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1077-L1096

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.eulerProduct_comparison (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    eulerProduct N 1 ≤ eulerProduct N (1 + r) *
      Real.exp (2 * r * ∑ p ∈ N.primesLE, Real.log p / p) := by sorry
