-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedSeriesJet_columnMonomial_eq_matrix_entry
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weightedSeriesJet_columnMonomial_eq_matrix_entry
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T12:55:19.477587+00:00
-- url     : https://prove2.me/theorems/b1b9403c-c452-4788-ba53-c63776d0920d
-- title:
--   Identify a column monomial coefficient with its matrix entry
-- statement:
--   For each row and column, the coefficient selected by the weighted-series jet of that column monomial equals the corresponding interpolation-matrix entry.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ColumnCombination

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weightedSeriesJet_columnMonomial_eq_matrix_entry
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (x : InterpolationMatrix.Column w0 w H → ℂ)
    (rho : InterpolationMatrix.Row K v0 theta w H)
    (c : InterpolationMatrix.Column w0 w H) :
  weightedSeriesJet v0 (fun i => w i / theta) H
      (fun i => (rho.1.val : ℂ) * r i) (fun i => (G i : PowerSeries ℂ))
      (columnMonomial w0 w H c) rho.2 =
    InterpolationMatrix.matrix K w0 v0 theta w H r G rho c := by sorry
