-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_subst_liftLogSeries_of_X_zero
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.subst_liftLogSeries_of_X_zero
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T06:08:04.690837+00:00
-- url     : https://prove2.me/theorems/5d7251ca-9292-44da-b052-657f5d030cdc
-- title:
--   Substitution fixing the distinguished variable preserves lifted series
-- statement:
--   An admissible substitution fixing $X_0$ leaves unchanged a lifted univariate series, since the lift depends only on $X_0$.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.subst_liftLogSeries_of_X_zero
    {m : ℕ} (F : PowerSeries ℂ)
    (a : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (ha : MvPowerSeries.HasSubst a) (h0 : a 0 = MvPowerSeries.X 0) :
    MvPowerSeries.subst a (liftLogSeries m F) = liftLogSeries m F := by sorry
