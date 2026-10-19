-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_lattice_boxes_volume_bound
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_volume_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T02:56:14.294023+00:00
-- url     : https://prove2.me/theorems/b2b25de5-442a-4d0c-a31f-1580ec40b776
-- title:
--   Volume bound for weighted lattice boxes
-- statement:
--   The total volume of the weight-sized boxes anchored at a finite set of nonnegative lattice points is at most the volume of the nonnegative simplex with cutoff enlarged by the sum of the weights.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_volume_bound
    (m : ℕ) (s : Finset (Fin m → ℕ)) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T)
    (hs : ∀ a ∈ s, ∑ i : Fin m, w i * (a i : ℝ) ≤ T) :
    ((s.card : ℝ) * ∏ i : Fin m, w i) ≤
      (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧
          ∑ i : Fin m, x i ≤ T + ∑ i : Fin m, w i}).toReal := by sorry
