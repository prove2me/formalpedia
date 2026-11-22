-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_coefficientMoment_sub_le
-- name    : LongGapsBetweenPrimes.coefficientMoment_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:17.764796+00:00
-- url     : https://prove2.me/theorems/664b725b-8f4e-428e-bb3f-053addebf345
-- title:
--   Long Gaps Between Primes: coefficient Moment sub le
-- statement:
--   Control the change in the squared moment by the absolute moment.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L214-L238
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L214-L238

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.coefficientMoment_sub_le {P : ℕ} (hP : 1 < P) (γ : ℝ) :
    coefficientMoment P γ - coefficientMoment P 0 ≤
      (γ / normalizer P) * coefficientAbsMoment P γ := by sorry
