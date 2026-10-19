-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftPowerSeries_coeff_formula
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.liftPowerSeries_coeff_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:55:12.446826+00:00
-- url     : https://prove2.me/theorems/519b97a1-622a-428d-a918-c3bc99e5055e
-- title:
--   Coefficient formula for a univariate series embedded in the zeroth coordinate
-- statement:
--   The coefficient at exponent vector d of the embedded univariate series is its coefficient at degree d(0) if every successor-coordinate exponent is zero, and otherwise is zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.liftPowerSeries_coeff_formula
    {m : ℕ} (f : PowerSeries ℂ)
    (d : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff d
      (((MvPowerSeries.finSuccEquiv ℂ m).symm.toRingHom.comp
        (PowerSeries.map MvPowerSeries.C)) f) =
      if ∀ j : Fin m, d j.succ = 0 then PowerSeries.coeff (d 0) f else 0 := by sorry
