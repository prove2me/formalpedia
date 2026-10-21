-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_subst_liftLogSeries_fixed
-- name    : OAI.PiExponent.LogarithmicJetIdeals.subst_liftLogSeries_fixed
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T06:11:46.5128+00:00
-- url     : https://prove2.me/theorems/bec867d1-6183-4b2b-b1fd-914e9a152f9f
-- title:
--   Substitution fixing the first variable fixes lifted series
-- statement:
--   Every admissible substitution fixing the first formal variable preserves every power series lifted through that variable, with no restriction on its constant coefficient.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.subst_liftLogSeries_fixed
    {m : ℕ} (a : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (ha : MvPowerSeries.HasSubst a) (ha0 : a 0 = MvPowerSeries.X 0)
    (f : PowerSeries ℂ) :
    MvPowerSeries.subst a
      (OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries m f) =
        OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries m f := by sorry
