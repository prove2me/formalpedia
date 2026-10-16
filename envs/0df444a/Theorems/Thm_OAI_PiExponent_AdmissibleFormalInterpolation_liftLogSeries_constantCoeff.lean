-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_constantCoeff
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_constantCoeff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T06:07:39.487984+00:00
-- url     : https://prove2.me/theorems/62dc7dad-78ae-44ba-a1bb-7dca9a0627da
-- title:
--   Constant coefficient of a lifted series
-- statement:
--   The multivariate constant coefficient of the lift of a univariate power series is its original constant coefficient.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_constantCoeff
    {m : ℕ} (F : PowerSeries ℂ) :
    MvPowerSeries.constantCoeff (liftLogSeries m F) = PowerSeries.coeff 0 F := by sorry
