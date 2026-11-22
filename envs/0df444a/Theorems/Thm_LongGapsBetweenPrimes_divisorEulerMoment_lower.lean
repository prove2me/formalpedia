-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_divisorEulerMoment_lower
-- name    : LongGapsBetweenPrimes.divisorEulerMoment_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:18.512901+00:00
-- url     : https://prove2.me/theorems/1edc7944-e62d-4484-b0dc-e73d1d5ffcbc
-- title:
--   Long Gaps Between Primes: divisor Euler Moment lower
-- statement:
--   The lower bound whose integral supplies a positive normalization B.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1287-L1300
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1287-L1300

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.divisorEulerMoment_lower {Z Y : ℕ} (hZY : Z ≤ Y) {t A : ℝ}
    (ht : 0 < t) (hA : 0 < A) (hZA : eulerProduct Z 1 ≤ A)
    (hscale : 1 ≤ t * Real.log ((Y : ℝ) + 1)) :
    1 / (2 * t * A) ≤ divisorEulerMoment (auxiliaryProduct Z Y) (-t) := by sorry
