-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedShear_coeff_eq_finite_sum
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_coeff_eq_finite_sum
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T16:42:40.766572+00:00
-- url     : https://prove2.me/theorems/70a160d9-6436-49f8-a6b5-44408bc885f5
-- title:
--   Weighted shear coefficients depend only on the retained strict simplex
-- statement:
--   With positive variable weights, assume delta_i vanishes in degrees strictly below T_i and u_i ≤ T_i v0. Every retained coefficient after shearing an arbitrary formal power series is the finite sum of its retained source coefficients multiplied by the corresponding sheared-monomial coefficients. The hypotheses force T_i ≥ 1. Equality in the weight bound is allowed, and H is arbitrary.
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

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_coeff_eq_finite_sum
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (T : Fin m → ℕ) (delta : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hT : ∀ i, u i ≤ (T i : ℝ) * v0)
    (hdelta : ∀ i (n : ℕ), n < T i → PowerSeries.coeff n (delta i) = 0)
    (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (a : ↥(strictWeightedSimplex (Fin.cases v0 u) H)) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
        (MvPowerSeries.subst
          (Fin.cases (MvPowerSeries.X (0 : Fin (m + 1)))
            (fun i : Fin m =>
              MvPowerSeries.X i.succ + liftLogSeries m (delta i))) F) =
      ∑ b : ↥(strictWeightedSimplex (Fin.cases v0 u) H),
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
            (formalShear delta
              (MvPolynomial.monomial (InterpolationMatrix.exponentVector b.val) 1)) *
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val) F := by sorry
