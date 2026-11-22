-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_sum_one_exception
-- name    : LongGapsBetweenPrimes.sum_one_exception
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:42.354802+00:00
-- url     : https://prove2.me/theorems/9f9979df-fa5b-4622-9552-997b37d3a627
-- title:
--   Long Gaps Between Primes: sum one exception
-- statement:
--   Sum a constant function with one exceptional value.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L127-L130
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L127-L130

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.sum_one_exception {p : ℕ} (a : Fin p) (c d : ℝ) :
    (∑ t : Fin p, if t = a then c else d) = c + ((p : ℝ) - 1) * d := by sorry
