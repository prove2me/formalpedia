-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_coeff_sum_support_monomials
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_coeff_sum_support_monomials
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T17:06:00.863163+00:00
-- url     : https://prove2.me/theorems/45fecfe4-0bc3-4d25-906d-68c87ef8fb1d
-- title:
--   Shear coefficient expands over polynomial support
-- statement:
--   The coefficient of a polynomial after applying the shear is the finite sum of the corresponding coefficients for its supported monomials, weighted by the original polynomial coefficients.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_coeff_sum_support_monomials
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e : Fin (m + 1) →₀ ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPowerSeries.coeff e (formalShear delta P) =
      ∑ a ∈ P.support,
        MvPolynomial.coeff a P *
          MvPowerSeries.coeff e (formalShear delta (MvPolynomial.monomial a 1)) := by sorry
