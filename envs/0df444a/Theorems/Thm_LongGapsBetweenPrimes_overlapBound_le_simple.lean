-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_overlapBound_le_simple
-- name    : LongGapsBetweenPrimes.overlapBound_le_simple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:40.679811+00:00
-- url     : https://prove2.me/theorems/2cd08e7f-ef55-4221-a346-114052800fd8
-- title:
--   Long Gaps Between Primes: overlap Bound le simple
-- statement:
--   The overlap contribution is at most `1 / (log 2 * x ^ 3)`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3351-L3358
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3351-L3358

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.overlapBound_le_simple {M x : ℝ} (hx : 0 < x) (hM : x ^ 4 ≤ M) :
    4 * Real.log (sieveD x) / (M * Real.log 2) ≤ 1 / (Real.log 2 * x ^ 3) := by sorry
