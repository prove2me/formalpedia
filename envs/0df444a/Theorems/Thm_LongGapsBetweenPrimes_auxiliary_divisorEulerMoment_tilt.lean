-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_auxiliary_divisorEulerMoment_tilt
-- name    : LongGapsBetweenPrimes.auxiliary_divisorEulerMoment_tilt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:57.255587+00:00
-- url     : https://prove2.me/theorems/59ed9657-fb32-4e5c-b490-8da35725c4fe
-- title:
--   Long Gaps Between Primes: auxiliary divisor Euler Moment tilt
-- statement:
--   Uniformly bound the cost of tilting the auxiliary divisor moment.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1533-L1564
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1533-L1564

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.auxiliary_divisorEulerMoment_tilt {Z Y : ℕ} (hY : 2 ≤ Y)
    {γ : ℝ} (hγ : 0 ≤ γ) (hscale : γ * Real.log Y ≤ 2) :
    divisorEulerMoment (auxiliaryProduct Z Y) γ ≤
      divisorEulerMoment (auxiliaryProduct Z Y) 0 * Real.exp (6 * Real.exp 2) := by sorry
