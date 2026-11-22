-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_sum_tupleMass_mul_rpow
-- name    : LongGapsBetweenPrimes.sum_tupleMass_mul_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:32:54.030714+00:00
-- url     : https://prove2.me/theorems/a1e073b7-cfcf-4091-8b3a-f28ce1660482
-- title:
--   Long Gaps Between Primes: sum tuple Mass mul rpow
-- statement:
--   The tilted tuple mass factors as a power of the coefficient moment.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L300-L311
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L300-L311

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.sum_tupleMass_mul_rpow (P k : ℕ) (γ : ℝ) :
    (∑ r : DivisorTuple P k, tupleMass r * (tupleProduct r : ℝ) ^ γ) =
      coefficientMoment P γ ^ k := by sorry
