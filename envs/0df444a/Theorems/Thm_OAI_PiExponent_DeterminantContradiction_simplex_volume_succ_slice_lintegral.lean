-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_succ_slice_lintegral
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_volume_succ_slice_lintegral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:19:59.768045+00:00
-- url     : https://prove2.me/theorems/a91269ca-701e-49ba-bbb7-e8c17a733517
-- title:
--   Simplex volume as an integral of slices
-- statement:
--   Decompose the volume of the positive-coordinate simplex into the integral of the volumes of its lower-dimensional slices. This removes the product-measure and fiber-identification step from the parent. Prove it by identifying Fin (m + 1) coordinates with Fin m coordinates and one real coordinate, applying product-measure integration to the measurable simplex, and describing each fiber by its inequalities. The bounds 0 ≤ t < T ensure the fiber has positive size; at m = 0 the fiber is the zero-dimensional simplex.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators
open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.simplex_volume_succ_slice_lintegral (m : Nat) (T : Real) (hT : 0 < T) :
    MeasureTheory.volume {x : Fin (m + 1) → Real |
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} =
      MeasureTheory.lintegral MeasureTheory.volume (fun t : Real =>
        if 0 ≤ t ∧ t < T then
          MeasureTheory.volume {x : Fin m → Real |
            (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T - t}
        else 0) := by sorry
