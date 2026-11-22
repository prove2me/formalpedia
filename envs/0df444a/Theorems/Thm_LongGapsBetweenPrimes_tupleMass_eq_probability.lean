-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_tupleMass_eq_probability
-- name    : LongGapsBetweenPrimes.tupleMass_eq_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:25.689656+00:00
-- url     : https://prove2.me/theorems/bde0e1dd-3ed3-4462-baa2-edf091d26452
-- title:
--   Long Gaps Between Primes: tuple Mass eq probability
-- statement:
--   Tuple mass is a fixed scale times the product of the divisor probabilities.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1876-L1881
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1876-L1881

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.tupleMass_eq_probability {P k : ℕ} (hP : P ≠ 0) (r : DivisorTuple P k) :
    tupleMass r = coefficientMoment P 0 ^ k * ∏ i, divisorProbability P (r i) := by sorry
