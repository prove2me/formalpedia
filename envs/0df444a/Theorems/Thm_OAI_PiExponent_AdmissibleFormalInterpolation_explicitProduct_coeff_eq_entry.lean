-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_explicitProduct_coeff_eq_entry
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.explicitProduct_coeff_eq_entry
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T16:35:33.844007+00:00
-- url     : https://prove2.me/theorems/1ed887eb-a51f-4553-9b68-d372e57eeddb
-- title:
--   Coefficient of the formal product equals the interpolation entry
-- statement:
--   The coefficient of the explicit formal product at distinguished degree s and remaining degrees b equals the corresponding interpolation matrix entry.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ColumnCombination

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.explicitProduct_coeff_eq_entry
    {m : ℕ} (j s : ℕ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (h : ℕ) (a b : Fin m → ℕ) :
  MvPowerSeries.coeff (InterpolationMatrix.exponentVector (Fin.cases s b))
      ((1 + MvPowerSeries.X 0) ^ h *
        ∏ i, (MvPowerSeries.C ((j : ℂ) * r i) + MvPowerSeries.X i.succ +
          liftLogSeries m (G i : PowerSeries ℂ)) ^ a i) =
    InterpolationMatrix.entry r G j s b h a := by sorry
