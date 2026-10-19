-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_lattice_boxes_union_volume_le_expanded_simplex
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_union_volume_le_expanded_simplex
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:14:14.877641+00:00
-- url     : https://prove2.me/theorems/ac54ed3d-2970-4aed-8826-cf4908598121
-- title:
--   Weighted lattice box union lies within the expanded simplex in volume
-- statement:
--   Under the target hypotheses, the union of the weighted half-open boxes has volume at most that of the nonnegative simplex with cutoff enlarged by the sum of the weights. Each box lies inside that simplex.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_union_volume_le_expanded_simplex
    (m : ℕ) (s : Finset (Fin m → ℕ)) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T)
    (hs : ∀ a ∈ s, ∑ i : Fin m, w i * (a i : ℝ) ≤ T) :
    (MeasureTheory.volume
      (⋃ a ∈ (s : Set (Fin m → ℕ)),
        {x : Fin m → ℝ | ∀ i,
          w i * (a i : ℝ) ≤ x i ∧ x i < w i * ((a i : ℝ) + 1)})).toReal ≤
      (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧
          ∑ i : Fin m, x i ≤ T + ∑ i : Fin m, w i}).toReal := by sorry
