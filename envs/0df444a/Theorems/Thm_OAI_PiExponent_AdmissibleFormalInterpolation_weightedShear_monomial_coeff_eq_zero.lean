-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedShear_monomial_coeff_eq_zero
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_monomial_coeff_eq_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T16:51:03.74288+00:00
-- url     : https://prove2.me/theorems/42e15162-5087-4d22-a5f3-e175156a56e4
-- title:
--   Weighted shear excludes source monomials outside the strict simplex
-- statement:
--   With positive weights and the stated vanishing orders, a retained target exponent receives no contribution from a source monomial outside the strict weighted simplex. Replacing a coordinate factor by a term of δᵢ preserves or increases weighted degree; the target has weight strictly below H.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_monomial_coeff_eq_zero
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (T : Fin m → ℕ) (delta : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hT : ∀ i, u i ≤ (T i : ℝ) * v0)
    (hdelta : ∀ i (n : ℕ), n < T i → PowerSeries.coeff n (delta i) = 0)
    (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (a : ↥(strictWeightedSimplex (Fin.cases v0 u) H))
    (b : Fin (m + 1) → ℕ)
    (hb : b ∉ strictWeightedSimplex (Fin.cases v0 u) H) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
      (formalShear delta
        (MvPolynomial.monomial (InterpolationMatrix.exponentVector b) 1)) = 0 := by sorry
