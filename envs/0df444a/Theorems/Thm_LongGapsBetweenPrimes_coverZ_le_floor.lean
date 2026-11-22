-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_coverZ_le_floor
-- name    : LongGapsBetweenPrimes.coverZ_le_floor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:59.53317+00:00
-- url     : https://prove2.me/theorems/59e50575-9c49-4789-baaa-6e84f26140fb
-- title:
--   Long Gaps Between Primes: cover Z le floor
-- statement:
--   The smoothness cutoff is at most the integer part of `x`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3923-L3924
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3923-L3924

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.coverZ_le_floor {x : ℝ} (hx : 0 < x) (hz : coverLogZ x ≤ Real.log x) : coverZ x ≤ ⌊x⌋₊ := by sorry
