-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_finite_nat_cube_union_volume
-- name    : OAI.PiExponent.DeterminantContradiction.finite_nat_cube_union_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:03:35.213807+00:00
-- url     : https://prove2.me/theorems/7107fb6b-6712-42d5-9d2b-235d469cccbf
-- title:
--   Volume of a finite union of natural lattice cubes
-- statement:
--   For any finite set of natural-number vectors in dimension m, the union of their half-open unit cubes has volume equal to the number of vectors.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.finite_nat_cube_union_volume
    {m : ℕ} (S : Finset (Fin m → ℕ)) :
    MeasureTheory.volume {x : Fin m → ℝ | ∃ a ∈ S, ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1} =
      (S.card : ENNReal) := by sorry
