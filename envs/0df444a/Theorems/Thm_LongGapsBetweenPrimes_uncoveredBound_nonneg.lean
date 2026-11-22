-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_uncoveredBound_nonneg
-- name    : LongGapsBetweenPrimes.uncoveredBound_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:21.688492+00:00
-- url     : https://prove2.me/theorems/b7bae939-4d0d-466d-b1b1-4769ac614228
-- title:
--   Long Gaps Between Primes: uncovered Bound nonneg
-- statement:
--   The normalized uncovered bound is nonnegative.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3215-L3216
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3215-L3216

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.uncoveredBound_nonneg (k : ℕ) (β C M : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ uncoveredBound k β C M D := by sorry
