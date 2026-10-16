-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_generator_logTail_coeff_support_succ
-- name    : OAI.PiExponent.LogarithmicJetIdeals.local_jet_generator_logTail_coeff_support_succ
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T20:40:50.209434+00:00
-- url     : https://prove2.me/theorems/5f7096a1-2a28-41ea-86a4-a131896675a8
-- title:
--   Logarithmic tail coefficient support
-- statement:
--   A nonzero coefficient of the lifted logarithmic remainder is supported only at coordinate zero and has degree at least the cutoff. Equality is allowed, and cutoff zero requires no positivity hypothesis.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.local_jet_generator_logTail_coeff_support_succ
    {m : ℕ} (T : Fin m → ℕ) (b : Fin (m + 1) → ℕ) (i : Fin m) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (AdmissibleFormalInterpolation.liftLogSeries m
        (PowerSeries.log ℂ -
          (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ))) ≠ 0 →
      (∀ j : Fin m, b j.succ = 0) ∧ T i ≤ b 0 := by sorry
