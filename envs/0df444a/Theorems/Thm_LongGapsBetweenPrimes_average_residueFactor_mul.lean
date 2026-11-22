-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_average_residueFactor_mul
-- name    : LongGapsBetweenPrimes.average_residueFactor_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:22.625623+00:00
-- url     : https://prove2.me/theorems/dd8de1d2-a1ae-4ad5-a7be-4425c2712470
-- title:
--   Long Gaps Between Primes: average residue Factor mul
-- statement:
--   Distinct residue factors have covariance `-1 / (p - 1)^2`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L529-L534
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L529-L534

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.average_residueFactor_mul {p : ℕ} (hp : 1 < p) (a b : Fin p) (hab : a ≠ b) :
    Finset.expect Finset.univ (fun t => residueFactor a t * residueFactor b t) =
      -1 / ((p : ℝ) - 1) ^ 2 := by sorry
