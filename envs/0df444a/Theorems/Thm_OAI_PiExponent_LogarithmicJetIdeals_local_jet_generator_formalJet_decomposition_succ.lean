-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_generator_formalJet_decomposition_succ
-- name    : OAI.PiExponent.LogarithmicJetIdeals.local_jet_generator_formalJet_decomposition_succ
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T20:39:55.112525+00:00
-- url     : https://prove2.me/theorems/bfa34f3d-39ca-440d-acd8-593f2bc4ca16
-- title:
--   Successor jet coefficient decomposition
-- statement:
--   Each coefficient of the formal image of a successor jet generator is the sum of the corresponding successor-variable coefficient and lifted logarithmic-tail coefficient, for arbitrary complex parameters and every natural cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.local_jet_generator_formalJet_decomposition_succ
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (b : Fin (m + 1) → ℕ) (i : Fin m) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (AdmissibleFormalInterpolation.formalJet c
        (jetCoordinate c T i.succ)) =
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (MvPowerSeries.X i.succ) +
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (AdmissibleFormalInterpolation.liftLogSeries m
          (PowerSeries.log ℂ -
            (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ))) := by sorry
