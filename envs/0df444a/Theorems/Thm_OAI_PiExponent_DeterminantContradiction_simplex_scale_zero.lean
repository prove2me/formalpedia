-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_scale_zero
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_scale_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T20:21:21.555455+00:00
-- url     : https://prove2.me/theorems/c539e0d0-f020-4b47-829c-01b41e11d29f
-- title:
--   Volume identity at zero scale
-- statement:
--   At cutoff zero, the identity holds in every dimension: for k > 0 the set is the singleton zero vector and has zero volume; for k = 0 both sides equal 1. This isolates the singular scale that the invertible linear-map change-of-variables argument cannot handle. The proof route is to characterize the cutoff-zero set, use nullity of a singleton in positive-dimensional Euclidean space, and simplify separately in dimension zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_scale_zero (k : ℕ) :
    (MeasureTheory.volume
      {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 0}).toReal =
      (0 ^ k) * (MeasureTheory.volume
        {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 1}).toReal := by sorry
