-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_sum_residueFactor_mul
-- name    : LongGapsBetweenPrimes.sum_residueFactor_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:40.772227+00:00
-- url     : https://prove2.me/theorems/52c5e998-242e-4c00-8191-579726e2079e
-- title:
--   Long Gaps Between Primes: sum residue Factor mul
-- statement:
--   Distinct roots have negative covariance, as used in (3.9).
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L147-L162
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L147-L162

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.sum_residueFactor_mul {p : ℕ} (hp : 1 < p) (a b : Fin p) (hab : a ≠ b) :
    (∑ t : Fin p, residueFactor a t * residueFactor b t) =
      -(p : ℝ) / ((p : ℝ) - 1) ^ 2 := by sorry
