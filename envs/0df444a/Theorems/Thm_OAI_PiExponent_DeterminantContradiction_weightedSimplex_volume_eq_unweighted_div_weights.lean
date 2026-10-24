-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_volume_eq_unweighted_div_weights
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_eq_unweighted_div_weights
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:08:41.307926+00:00
-- url     : https://prove2.me/theorems/07c628e6-75bf-468e-99c9-12728f37fb60
-- title:
--   Weighted simplex volume by diagonal scaling
-- statement:
--   The weighted simplex volume equals the unweighted simplex volume divided by the product of the positive coordinate weights.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_eq_unweighted_div_weights {m : Nat} (w : Fin m → Real) (H : Real) (hw : ∀ i, 0 < w i) (hH : 0 < H) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ H}).toReal =
      (MeasureTheory.volume {y : Fin m → Real | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ H}).toReal / ∏ i : Fin m, w i := by sorry
