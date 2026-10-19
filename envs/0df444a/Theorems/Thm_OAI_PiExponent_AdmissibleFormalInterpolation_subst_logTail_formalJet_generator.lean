-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_subst_logTail_formalJet_generator
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.subst_logTail_formalJet_generator
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:00:51.929768+00:00
-- url     : https://prove2.me/theorems/4f4298e5-c70c-4654-9f3d-208f70ea1cc9
-- title:
--   Log-tail substitution on polynomial generators
-- statement:
--   For each polynomial variable, substituting the logarithmic correction into its formal-jet image yields its truncated formal-jet image. The zeroth variable is fixed; each positive variable has its logarithmic term canceled by the correction, including when its truncation order is zero.
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

theorem OAI.PiExponent.AdmissibleFormalInterpolation.subst_logTail_formalJet_generator
    {m : ℕ} (T : Fin m → ℕ) (c : Fin m → ℂ)
    (s : Fin (m + 1)) :
    MvPowerSeries.subst
        (Fin.cases (MvPowerSeries.X (0 : Fin (m + 1)))
          (fun i : Fin m =>
            MvPowerSeries.X i.succ +
              liftLogSeries m
                ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
                  PowerSeries.log ℂ)))
        (formalJet c (MvPolynomial.X s)) =
      truncatedFormalJet T c (MvPolynomial.X s) := by sorry
