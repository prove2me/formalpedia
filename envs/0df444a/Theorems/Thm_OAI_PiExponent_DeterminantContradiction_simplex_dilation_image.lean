-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_dilation_image
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_dilation_image
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T21:21:08.93013+00:00
-- url     : https://prove2.me/theorems/1e4bab43-bfd4-4716-b8a2-e922425d7efc
-- title:
--   Cutoff simplex as a dilation image
-- statement:
--   The simplex with cutoff a is the image of the unit simplex under coordinatewise multiplication by a.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_dilation_image (m : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ a} =
      Set.image (fun x : Fin m → ℝ => a • x)
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ 1} := by sorry
