-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_normalizer_integral_le
-- name    : LongGapsBetweenPrimes.normalizer_integral_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:35.918826+00:00
-- url     : https://prove2.me/theorems/495f8101-8e78-42d4-9e99-bdb213ed7743
-- title:
--   Long Gaps Between Primes: normalizer integral le
-- statement:
--   The normalizer dominates every positive-half-line integral of U_(-t)-1.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1322-L1350
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1322-L1350

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.normalizer_integral_le {P : ℕ} (hP : P ≠ 0) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    (∫ t : ℝ in a..b, divisorEulerMoment P (-t) - 1) ≤ normalizer P := by sorry
