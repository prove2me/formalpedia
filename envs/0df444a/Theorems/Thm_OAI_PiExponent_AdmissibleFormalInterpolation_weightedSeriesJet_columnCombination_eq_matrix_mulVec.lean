-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedSeriesJet_columnCombination_eq_matrix_mulVec
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weightedSeriesJet_columnCombination_eq_matrix_mulVec
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:48:23.979106+00:00
-- url     : https://prove2.me/theorems/f7b98a26-255b-4b87-b7e9-a3993c4cacb3
-- title:
--   The jet of the column combination is the matrix-vector product
-- statement:
--   For each row, the weighted-series jet coefficient of the finite column combination equals the matrix-vector product. This follows by distributing coefficient extraction over the sum and matching each monomial’s substitution coefficient with the matrix entry.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ColumnCombination

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weightedSeriesJet_columnCombination_eq_matrix_mulVec
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (x : InterpolationMatrix.Column w0 w H → ℂ) :
    ∀ rho : InterpolationMatrix.Row K v0 theta w H,
      weightedSeriesJet v0 (fun i => w i / theta) H
        (fun i => (rho.1.val : ℂ) * r i) (fun i => (G i : PowerSeries ℂ))
        (columnCombination w0 w H x) rho.2 =
      ((InterpolationMatrix.matrix K w0 v0 theta w H r G).mulVecLin x) rho := by sorry
