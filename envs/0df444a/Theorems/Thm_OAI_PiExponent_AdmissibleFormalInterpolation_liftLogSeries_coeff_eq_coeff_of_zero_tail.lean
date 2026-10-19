-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_coeff_eq_coeff_of_zero_tail
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_coeff_eq_coeff_of_zero_tail
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T07:18:24.235363+00:00
-- url     : https://prove2.me/theorems/821c1e47-c24f-4889-8b2e-12020c154703
-- title:
--   Lifted-series coefficients on coordinate zero
-- statement:
--   When all successor coordinates of the exponent vanish, the lifted coefficient is exactly the original univariate coefficient at the coordinate-zero degree. This is the supported-exponent coefficient identity.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_coeff_eq_coeff_of_zero_tail
    (m : ℕ) (D : PowerSeries ℂ) (α : Fin (m + 1) →₀ ℕ)
    (htail : ∀ j : Fin m, α j.succ = 0) :
    MvPowerSeries.coeff α (OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries m D) =
      PowerSeries.coeff (α 0) D := by sorry
