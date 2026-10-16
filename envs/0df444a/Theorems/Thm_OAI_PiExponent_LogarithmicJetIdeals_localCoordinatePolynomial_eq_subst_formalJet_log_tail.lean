-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_localCoordinatePolynomial_eq_subst_formalJet_log_tail
-- name    : OAI.PiExponent.LogarithmicJetIdeals.localCoordinatePolynomial_eq_subst_formalJet_log_tail
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T05:41:34.074917+00:00
-- url     : https://prove2.me/theorems/e7120eb8-3d4c-489e-b074-dda8dba781fa
-- title:
--   Truncated logarithmic local coordinates arise by a formal tail substitution
-- statement:
--   The local-coordinate polynomial embedded into formal power series equals the formal jet after fixing the initial variable and adding truncated-logarithm minus full-logarithm tails to the other variables. The tails cancel the full logarithm on polynomial generators. No weight or positivity assumptions are needed, and zero truncation cutoffs are allowed.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinates
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.localCoordinatePolynomial_eq_subst_formalJet_log_tail
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    (localCoordinatePolynomial c T P : MvPowerSeries (Fin (m + 1)) ℂ) =
      MvPowerSeries.subst
        (Fin.cases (MvPowerSeries.X 0)
          (fun i : Fin m => MvPowerSeries.X i.succ + liftLogSeries m
            ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
              PowerSeries.log ℂ)))
        (formalJet c P) := by sorry
