-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_continuous_divisorEulerMoment
-- name    : LongGapsBetweenPrimes.continuous_divisorEulerMoment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:21.545739+00:00
-- url     : https://prove2.me/theorems/df6ec0af-5242-4b9c-b983-ec1d1663eba1
-- title:
--   Long Gaps Between Primes: continuous divisor Euler Moment
-- statement:
--   The negatively tilted divisor Euler moment is continuous.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1303-L1310
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1303-L1310

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.continuous_divisorEulerMoment (P : ℕ) :
    Continuous (fun t : ℝ => divisorEulerMoment P (-t)) := by sorry
