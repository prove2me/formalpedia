-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_hasSubst_logTailCoordinates
-- name    : OAI.PiExponent.LogarithmicJetIdeals.hasSubst_logTailCoordinates
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T06:11:25.234484+00:00
-- url     : https://prove2.me/theorems/6613ab63-fc88-4212-ad93-6570cd9472ff
-- title:
--   The logarithmic tail coordinates admit substitution
-- statement:
--   For every family of natural-number truncation cutoffs, the logarithmic-tail coordinate family satisfies the power-series substitution condition, including zero cutoffs and zero additional variables.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.hasSubst_logTailCoordinates
    {m : ℕ} (T : Fin m → ℕ) :
    MvPowerSeries.HasSubst
      (Fin.cases (MvPowerSeries.X 0)
        (fun i : Fin m => MvPowerSeries.X i.succ +
          OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries m
            ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) - PowerSeries.log ℂ))) := by sorry
