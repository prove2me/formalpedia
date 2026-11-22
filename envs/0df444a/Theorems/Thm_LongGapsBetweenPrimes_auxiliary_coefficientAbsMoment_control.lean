-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_auxiliary_coefficientAbsMoment_control
-- name    : LongGapsBetweenPrimes.auxiliary_coefficientAbsMoment_control
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:06.840346+00:00
-- url     : https://prove2.me/theorems/667c88bf-40b8-4d41-a6ca-ce2ecee5ab14
-- title:
--   Long Gaps Between Primes: auxiliary coefficient Abs Moment control
-- statement:
--   Bound the auxiliary absolute moment by a constant times the normalizer.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1654-L1664
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1654-L1664

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.auxiliary_coefficientAbsMoment_control {Z Y : ℕ} (hZY : Z ≤ Y) (hZ : 2 ≤ Z)
    (hlogZ : 1 ≤ Real.log Z) (hP : 1 < auxiliaryProduct Z Y)
    {b γ : ℝ} (hb : 0 < b) (hB : b ≤ normalizer (auxiliaryProduct Z Y))
    (hγ : 0 ≤ γ) (hscale : γ * Real.log Y ≤ 2) :
    coefficientAbsMoment (auxiliaryProduct Z Y) γ ≤
      coefficientControl b * normalizer (auxiliaryProduct Z Y) := by sorry
