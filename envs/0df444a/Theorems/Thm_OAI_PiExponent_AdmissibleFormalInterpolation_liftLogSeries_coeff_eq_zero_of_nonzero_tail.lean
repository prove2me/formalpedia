-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_coeff_eq_zero_of_nonzero_tail
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_coeff_eq_zero_of_nonzero_tail
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T07:17:56.856285+00:00
-- url     : https://prove2.me/theorems/37cd248e-0ff6-4d20-ba6f-aefb6f4a34af
-- title:
--   Lifted-series coefficients vanish off coordinate zero
-- statement:
--   If an exponent has a nonzero coordinate after coordinate zero, its coefficient in the lift of a univariate power series is zero. This isolates the unsupported-exponent case and is independent of all weight assumptions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_coeff_eq_zero_of_nonzero_tail
    (m : ℕ) (D : PowerSeries ℂ) (α : Fin (m + 1) →₀ ℕ)
    (htail : ∃ j : Fin m, α j.succ ≠ 0) :
    MvPowerSeries.coeff α (OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries m D) = 0 := by sorry
