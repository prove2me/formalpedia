-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_divisorEulerMoment_zero_le
-- name    : LongGapsBetweenPrimes.divisorEulerMoment_zero_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:49.9413+00:00
-- url     : https://prove2.me/theorems/f4562c0a-30bb-44b5-a4ee-d7e8b3091039
-- title:
--   Long Gaps Between Primes: divisor Euler Moment zero le
-- statement:
--   Bound the auxiliary zero moment by a ratio of logarithms.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1477-L1486
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1477-L1486

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.divisorEulerMoment_zero_le {Z Y : ℕ} (hZY : Z ≤ Y) (hZ : 2 ≤ Z) :
    divisorEulerMoment (auxiliaryProduct Z Y) 0 ≤
      Real.exp 6 * (1 + Real.log Y) / Real.log Z := by sorry
