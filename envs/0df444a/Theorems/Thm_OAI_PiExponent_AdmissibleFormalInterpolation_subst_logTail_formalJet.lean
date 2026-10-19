-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_subst_logTail_formalJet
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.subst_logTail_formalJet
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:07:44.662829+00:00
-- url     : https://prove2.me/theorems/1aac463a-2097-4aee-8d53-82eaaabd4bd3
-- title:
--   Log-tail substitution on polynomial formal jets
-- statement:
--   For every polynomial in the distinguished variable and the remaining variables, substituting the logarithmic correction into its formal-jet image yields its truncated formal-jet image.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation_TruncatedJet
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.subst_logTail_formalJet
    {m : ℕ} (T : Fin m → ℕ) (c : Fin m → ℂ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPowerSeries.subst
        (Fin.cases (MvPowerSeries.X (0 : Fin (m + 1)))
          (fun i : Fin m =>
            MvPowerSeries.X i.succ +
              liftLogSeries m
                ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
                  PowerSeries.log ℂ)))
        (formalJet c P) = truncatedFormalJet T c P := by sorry
