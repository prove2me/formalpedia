-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_lattice_boxes_union_ennreal_sum
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_union_ennreal_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:20:37.520984+00:00
-- url     : https://prove2.me/theorems/065d6e3f-7008-44f0-9b9e-586aac9b2b84
-- title:
--   ENNReal volume sum for weighted lattice boxes
-- statement:
--   The ENNReal volume of a finite union of weighted half-open lattice boxes is the sum, over the selected lattice vectors, of the product of the coordinate weights embedded in ENNReal. The boxes are measurable and pairwise disjoint because distinct integer vectors differ in at least one coordinate, where their half-open intervals do not overlap; each box has the indicated product volume.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_union_ennreal_sum
    (m : ℕ) (s : Finset (Fin m → ℕ)) (w : Fin m → ℝ)
    (hw : ∀ i, 0 < w i) :
    MeasureTheory.volume
      (⋃ a ∈ (s : Set (Fin m → ℕ)),
        {x : Fin m → ℝ | ∀ i,
          w i * (a i : ℝ) ≤ x i ∧ x i < w i * ((a i : ℝ) + 1)}) =
      ∑ a ∈ s, ∏ i : Fin m, ENNReal.ofReal (w i) := by sorry
