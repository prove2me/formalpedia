-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_scaled_image
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_scaled_image
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T21:16:43.564601+00:00
-- url     : https://prove2.me/theorems/f45d63c4-ecf8-48c1-934f-0411ae26b8ea
-- title:
--   The scaled simplex is the image of the unit simplex
-- statement:
--   For positive `U`, coordinatewise scalar multiplication by `U` maps the unit simplex in `Fin k → ℝ` exactly onto the simplex whose coordinate sum is at most `U`. Positivity is needed for the reverse scaling to preserve the coordinate and sum inequalities; the statement also holds for `k = 0`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_scaled_image (k : ℕ) (U : ℝ) (hU : 0 < U) :
    (fun x : Fin k → ℝ => U • x) ''
        {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 1} =
      {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ U} := by sorry
