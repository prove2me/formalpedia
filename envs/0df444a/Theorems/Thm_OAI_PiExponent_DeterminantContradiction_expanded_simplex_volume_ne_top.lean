-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_expanded_simplex_volume_ne_top
-- name    : OAI.PiExponent.DeterminantContradiction.expanded_simplex_volume_ne_top
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:33:17.951886+00:00
-- url     : https://prove2.me/theorems/e87b13ed-ee43-4091-8234-3ed7aab106cd
-- title:
--   Expanded simplex has finite volume
-- statement:
--   The expanded nonnegative simplex has finite volume. This provides the finiteness hypothesis needed to compare the real-valued volumes after establishing set inclusion.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.expanded_simplex_volume_ne_top
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T) :
    MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧
        ∑ i : Fin m, x i ≤ T + ∑ i : Fin m, w i} ≠ ⊤ := by sorry
