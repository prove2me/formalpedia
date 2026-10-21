-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_subst_logTail_formalJet_eq_truncatedFormalJet_of_generators
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.subst_logTail_formalJet_eq_truncatedFormalJet_of_generators
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:01:27.925548+00:00
-- url     : https://prove2.me/theorems/e6a2649c-c74e-481d-aede-218bd2c31da3
-- title:
--   Extend a substitution identity from polynomial generators
-- statement:
--   If substitution by the logarithmic correction agrees with the truncated formal jet on every polynomial variable, then it agrees on every multivariate polynomial. This is the algebra-hom extensionality step that lifts the generator calculation to arbitrary `P`.
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

theorem OAI.PiExponent.AdmissibleFormalInterpolation.subst_logTail_formalJet_eq_truncatedFormalJet_of_generators
    {m : ℕ} (T : Fin m → ℕ) (c : Fin m → ℂ)
    (hgen : ∀ s : Fin (m + 1),
      MvPowerSeries.subst
          (Fin.cases (MvPowerSeries.X (0 : Fin (m + 1)))
            (fun i : Fin m =>
              MvPowerSeries.X i.succ +
                liftLogSeries m
                  ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
                    PowerSeries.log ℂ)))
          (formalJet c (MvPolynomial.X s)) =
        truncatedFormalJet T c (MvPolynomial.X s))
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
