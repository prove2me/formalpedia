-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_subst_logTail_formalJet_eq_truncatedFormalJet
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.subst_logTail_formalJet_eq_truncatedFormalJet
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T16:43:17.495316+00:00
-- url     : https://prove2.me/theorems/117929aa-2e39-4467-bea6-729d0b0b81d8
-- title:
--   Logarithm-tail substitution turns the formal jet into the truncated formal jet
-- statement:
--   For any polynomial P, constants c, and natural truncation orders T, substituting X_i by X_i plus the lifted difference truncatedLog(T_i) − log, while fixing X_0, transforms formalJet(c,P) into truncatedFormalJet(T,c,P). This whole-series identity requires no support or weight bound and remains valid when T_i = 0.
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

theorem OAI.PiExponent.AdmissibleFormalInterpolation.subst_logTail_formalJet_eq_truncatedFormalJet
    {m : ℕ} (T : Fin m → ℕ) (c : Fin m → ℂ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPowerSeries.subst
        (Fin.cases (MvPowerSeries.X (0 : Fin (m + 1)))
          (fun i : Fin m =>
            MvPowerSeries.X i.succ +
              liftLogSeries m
                ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
                  PowerSeries.log ℂ)))
        (formalJet c P) =
      truncatedFormalJet T c P := by sorry
