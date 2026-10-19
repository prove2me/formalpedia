-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_dilation_eq_image
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_dilation_eq_image
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:01:17.079032+00:00
-- url     : https://prove2.me/theorems/f18c6a59-7d3a-4c33-abf6-12201c07bec0
-- title:
--   Simplex as a dilation image
-- statement:
--   For positive r, the simplex with coordinate sum at most r is exactly the image of the unit simplex under coordinatewise multiplication by r.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.simplex_dilation_eq_image
    (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ({x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ r} : Set (Fin n → ℝ)) =
      (fun x : Fin n → ℝ => r • x) ''
        {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)} := by sorry
