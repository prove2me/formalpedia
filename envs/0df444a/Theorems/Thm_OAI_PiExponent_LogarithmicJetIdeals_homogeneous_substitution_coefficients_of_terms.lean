-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_homogeneous_substitution_coefficients_of_terms
-- name    : OAI.PiExponent.LogarithmicJetIdeals.homogeneous_substitution_coefficients_of_terms
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:28:17.758751+00:00
-- url     : https://prove2.me/theorems/609ed128-d9ad-4e7f-8f72-e601eb978ab6
-- title:
--   Aggregate substituted monomial coefficients
-- statement:
--   If every supported monomial term of a polynomial has no substituted coefficients below D and has the same degree-D coefficients as that term, then the substituted polynomial has no coefficients below D and preserves its degree-D coefficients. This is the finite-support aggregation step.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.homogeneous_substitution_coefficients_of_terms
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (P : MvPolynomial (Fin n) Complex)
    (D : Nat)
    (e : Fin n → Nat)
    (hhom : ∀ m ∈ P.support, (∑ i, m i) = D)
    (hterm : ∀ m ∈ P.support,
      ((∑ i, e i) < D →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi
            (MvPolynomial.monomial m (MvPolynomial.coeff m P))) = 0) ∧
      ((∑ i, e i) = D →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi
            (MvPolynomial.monomial m (MvPolynomial.coeff m P))) =
              MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
                (MvPolynomial.monomial m (MvPolynomial.coeff m P)))) :
    ((∑ i, e i) < D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi P) = 0) ∧
    ((∑ i, e i) = D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi P) =
          MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) P) := by sorry
