-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_coefficientMoment_zero
-- name    : LongGapsBetweenPrimes.coefficientMoment_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:39.828132+00:00
-- url     : https://prove2.me/theorems/91c5b5b7-d3fb-4cd5-a1ee-29594d0d7300
-- title:
--   Long Gaps Between Primes: coefficient Moment zero
-- statement:
--   Expand the coefficient moment at exponent zero.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L180-L182
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L180-L182

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.coefficientMoment_zero (P : ℕ) :
    coefficientMoment P 0 = ∑ d ∈ P.divisors, coefficient P d ^ 2 / d.totient := by sorry
