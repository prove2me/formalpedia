-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_eq_diagonalScaling_image
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_eq_diagonalScaling_image
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:19:19.848416+00:00
-- url     : https://prove2.me/theorems/10119e5e-3609-4019-aae6-680e17353c01
-- title:
--   Weighted simplex as a diagonal image
-- statement:
--   The weighted simplex is exactly the image of the standard simplex under coordinatewise division by the positive weights.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_eq_diagonalScaling_image {m : Nat} (w : Fin m → Real) (H : Real) (hw : ∀ i, 0 < w i) :
    {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ H} =
      Set.image (fun y : Fin m → Real => fun i => y i / w i)
        {y : Fin m → Real | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ H} := by sorry
