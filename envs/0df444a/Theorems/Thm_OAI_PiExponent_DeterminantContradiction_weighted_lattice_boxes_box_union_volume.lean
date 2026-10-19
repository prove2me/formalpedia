-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_lattice_boxes_box_union_volume
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_box_union_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:13:54.174486+00:00
-- url     : https://prove2.me/theorems/1588aff9-4f47-43f6-9091-8f0e2fd604cf
-- title:
--   Volume of a union of weighted lattice boxes
-- statement:
--   For positive coordinate weights, the union of the half-open boxes anchored at the finite set of lattice vectors has volume equal to the number of vectors times the product of the weights. Distinct lattice vectors give boxes with disjoint interiors.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_box_union_volume
    (m : ℕ) (s : Finset (Fin m → ℕ)) (w : Fin m → ℝ)
    (hw : ∀ i, 0 < w i) :
    (MeasureTheory.volume
      (⋃ a ∈ (s : Set (Fin m → ℕ)),
        {x : Fin m → ℝ | ∀ i,
          w i * (a i : ℝ) ≤ x i ∧ x i < w i * ((a i : ℝ) + 1)})).toReal =
      (s.card : ℝ) * ∏ i : Fin m, w i := by sorry
