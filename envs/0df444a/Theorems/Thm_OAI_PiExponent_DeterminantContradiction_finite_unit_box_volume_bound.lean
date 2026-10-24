-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_finite_unit_box_volume_bound
-- name    : OAI.PiExponent.DeterminantContradiction.finite_unit_box_volume_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:08:22.32419+00:00
-- url     : https://prove2.me/theorems/6be72088-8225-47b1-a43d-c5510d3148ec
-- title:
--   Bound the volume of a finite union of integer unit boxes
-- statement:
--   A finite union of half-open unit boxes based at distinct nonnegative integer vectors has volume at most the number of vectors indexing the boxes.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.finite_unit_box_volume_bound {m : Nat} (S : Finset (Fin m → Nat)) :
    (MeasureTheory.volume (⋃ n ∈ S,
      {x : Fin m → Real | ∀ i, (n i : Real) ≤ x i ∧ x i < (n i : Real) + 1})).toReal ≤ (S.card : Real) := by sorry
