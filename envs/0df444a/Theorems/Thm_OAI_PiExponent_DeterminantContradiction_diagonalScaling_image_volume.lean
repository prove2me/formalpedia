-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_diagonalScaling_image_volume
-- name    : OAI.PiExponent.DeterminantContradiction.diagonalScaling_image_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:18:15.843662+00:00
-- url     : https://prove2.me/theorems/ff5fa03f-2c36-4647-9809-d443969df6da
-- title:
--   Volume of a diagonally scaled standard simplex
-- statement:
--   Scaling each coordinate of the standard simplex by the reciprocal of its positive weight scales its Lebesgue volume by the reciprocal of the product of the weights.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.diagonalScaling_image_volume {m : Nat} (w : Fin m → Real) (H : Real) (hw : ∀ i, 0 < w i) (hH : 0 < H) :
    (MeasureTheory.volume (Set.image (fun y : Fin m → Real => fun i => y i / w i)
      {y : Fin m → Real | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ H})).toReal =
      (MeasureTheory.volume {y : Fin m → Real | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ H}).toReal / ∏ i : Fin m, w i := by sorry
