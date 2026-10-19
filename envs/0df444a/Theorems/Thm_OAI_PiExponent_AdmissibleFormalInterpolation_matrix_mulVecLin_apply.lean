-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_matrix_mulVecLin_apply
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.matrix_mulVecLin_apply
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:55:53.710513+00:00
-- url     : https://prove2.me/theorems/6f42144d-9ebc-4633-be31-ad1d6597714c
-- title:
--   Express matrix-vector evaluation as a finite sum
-- statement:
--   Evaluating the matrix linear map at a row is the sum over columns of the matrix entry times the corresponding vector coordinate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ColumnCombination

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.matrix_mulVecLin_apply
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (x : InterpolationMatrix.Column w0 w H → ℂ)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
  ((InterpolationMatrix.matrix K w0 v0 theta w H r G).mulVecLin x) rho =
    ∑ c : InterpolationMatrix.Column w0 w H,
      InterpolationMatrix.matrix K w0 v0 theta w H r G rho c * x c := by sorry
