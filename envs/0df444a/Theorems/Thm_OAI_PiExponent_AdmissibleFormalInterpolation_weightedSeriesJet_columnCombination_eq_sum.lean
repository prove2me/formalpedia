-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedSeriesJet_columnCombination_eq_sum
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weightedSeriesJet_columnCombination_eq_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:54:45.422987+00:00
-- url     : https://prove2.me/theorems/5095b286-6a05-4734-a169-0cbad44c37d0
-- title:
--   Distribute the weighted-series jet over the column sum
-- statement:
--   The weighted-series jet of the finite column combination is the sum of each column's jet coefficient multiplied by its scalar weight.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ColumnCombination

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weightedSeriesJet_columnCombination_eq_sum
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (x : InterpolationMatrix.Column w0 w H → ℂ)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
  weightedSeriesJet v0 (fun i => w i / theta) H
      (fun i => (rho.1.val : ℂ) * r i) (fun i => (G i : PowerSeries ℂ))
      (columnCombination w0 w H x) rho.2 =
    ∑ c : InterpolationMatrix.Column w0 w H,
      x c * weightedSeriesJet v0 (fun i => w i / theta) H
        (fun i => (rho.1.val : ℂ) * r i) (fun i => (G i : PowerSeries ℂ))
        (columnMonomial w0 w H c) rho.2 := by sorry
