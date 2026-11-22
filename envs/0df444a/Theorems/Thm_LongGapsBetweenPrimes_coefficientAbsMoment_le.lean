-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_coefficientAbsMoment_le
-- name    : LongGapsBetweenPrimes.coefficientAbsMoment_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:35.537039+00:00
-- url     : https://prove2.me/theorems/91927044-15f5-42ea-acc1-06529ff7a09c
-- title:
--   Long Gaps Between Primes: coefficient Abs Moment le
-- statement:
--   Splitting at Y gives the tilted absolute-moment bound in (3.6).
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1409-L1458
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1409-L1458

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.coefficientAbsMoment_le {P Y : ℕ} (hP : 1 < P) (hY : 1 < Y)
    {γ E : ℝ} (hγ : 0 ≤ γ) (hYE : (Y : ℝ) ^ γ ≤ E) :
    coefficientAbsMoment P γ ≤ E + divisorEulerMoment P γ / (normalizer P * Real.log Y) := by sorry
