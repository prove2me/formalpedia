-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_subst_formalJet_log_tail_eq_truncatedCoordinate_aeval
-- name    : OAI.PiExponent.LogarithmicJetIdeals.subst_formalJet_log_tail_eq_truncatedCoordinate_aeval
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:48:42.180433+00:00
-- url     : https://prove2.me/theorems/96925ee8-8d7f-403b-add0-cbd103463a5b
-- title:
--   Substitution of a formal jet evaluates at truncated-log coordinates
-- statement:
--   Substituting into the formal jet is polynomial evaluation at the coordinates with the full logarithm canceled and replaced by its truncation.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinates
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.subst_formalJet_log_tail_eq_truncatedCoordinate_aeval
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPowerSeries.subst
        (Fin.cases (MvPowerSeries.X 0)
          (fun i : Fin m => MvPowerSeries.X i.succ + liftLogSeries m
            ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
              PowerSeries.log ℂ)))
        (formalJet c P) =
      MvPolynomial.aeval
        (Fin.cases (1 + MvPowerSeries.X 0)
          (fun i : Fin m => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
            liftLogSeries m (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ))) P := by sorry
