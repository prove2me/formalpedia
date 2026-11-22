-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_coefficientRemainder_eq_sum
-- name    : LongGapsBetweenPrimes.coefficientRemainder_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:35.384068+00:00
-- url     : https://prove2.me/theorems/9b9e0c76-b175-47bf-bb9b-f5e1a6a7d314
-- title:
--   Long Gaps Between Primes: coefficient Remainder eq sum
-- statement:
--   Express the coefficient remainder as a sum over divisor indices.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2757-L2763
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2757-L2763

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.coefficientRemainder_eq_sum (P m : ℕ) (D : ℝ) :
    coefficientRemainder P m D =
      ∑ d : DivisorIndex P,
        if (d.val : ℝ) ≤ D / m ∧ d.val.Coprime m then
          coefficient P d.val / d.val.totient else 0 := by sorry
