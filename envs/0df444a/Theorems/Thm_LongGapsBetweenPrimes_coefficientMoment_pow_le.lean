-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_coefficientMoment_pow_le
-- name    : LongGapsBetweenPrimes.coefficientMoment_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:32:56.557474+00:00
-- url     : https://prove2.me/theorems/a95d028c-d4b0-450b-9c46-e55d9e8e3b66
-- title:
--   Long Gaps Between Primes: coefficient Moment pow le
-- statement:
--   Bound powers of a tilted coefficient moment relative to the zero moment.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L336-L351
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L336-L351

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.coefficientMoment_pow_le {P : ℕ} (hP : 1 < P) {C γ : ℝ}
    (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hM : coefficientAbsMoment P γ ≤ C * normalizer P) (k : ℕ) :
    coefficientMoment P γ ^ k ≤
      coefficientMoment P 0 ^ k * Real.exp ((k : ℝ) * C * γ) := by sorry
