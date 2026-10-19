-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftPowerSeries_succ_support
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.liftPowerSeries_succ_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:48:24.854022+00:00
-- url     : https://prove2.me/theorems/ea655ade-2a36-43c0-ad3a-1a2988baf2c0
-- title:
--   Power series embedded in the zeroth coordinate have no successor-coordinate support
-- statement:
--   For any univariate complex power series, its embedding into the zeroth coordinate of a multivariate power series has zero coefficient whenever any successor coordinate has a nonzero exponent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.liftPowerSeries_succ_support
    {m : ℕ} (f : PowerSeries ℂ)
    (d : Fin (m + 1) →₀ ℕ) (j : Fin m) (h : d j.succ ≠ 0) :
    MvPowerSeries.coeff d
      (((MvPowerSeries.finSuccEquiv ℂ m).symm.toRingHom.comp
        (PowerSeries.map MvPowerSeries.C)) f) = 0 := by sorry
