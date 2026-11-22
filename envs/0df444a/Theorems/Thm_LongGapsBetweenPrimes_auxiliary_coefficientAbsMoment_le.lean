-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_auxiliary_coefficientAbsMoment_le
-- name    : LongGapsBetweenPrimes.auxiliary_coefficientAbsMoment_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:51.902313+00:00
-- url     : https://prove2.me/theorems/6c14f442-8dae-460d-bd0f-21c650a63af8
-- title:
--   Long Gaps Between Primes: auxiliary coefficient Abs Moment le
-- statement:
--   Bound the auxiliary absolute moment by `absoluteMomentBound`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1613-L1651
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1613-L1651

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.auxiliary_coefficientAbsMoment_le {Z Y : ℕ} (hZY : Z ≤ Y) (hZ : 2 ≤ Z)
    (hlogZ : 1 ≤ Real.log Z) (hP : 1 < auxiliaryProduct Z Y)
    {b γ : ℝ} (hb : 0 < b) (hB : b ≤ normalizer (auxiliaryProduct Z Y))
    (hγ : 0 ≤ γ) (hscale : γ * Real.log Y ≤ 2) :
    coefficientAbsMoment (auxiliaryProduct Z Y) γ ≤ absoluteMomentBound b := by sorry
