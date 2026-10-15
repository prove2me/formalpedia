-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finiteJet_interpolation_from_triangular
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finiteJet_interpolation_from_triangular
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T06:17:47.314057+00:00
-- url     : https://prove2.me/theorems/6d44e420-1e9d-45e0-bb99-0fdae9a5ff33
-- title:
--   Interpolation from triangular monomial coefficients
-- statement:
--   If substitution on monomials has no lower-degree terms and acts as the identity on each monomial's own degree, then a polynomial can be chosen to match any specified coefficients through degree $N$.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.finiteJet_interpolation_from_triangular
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (N : Nat)
    (hbelow : ∀ d e : Fin n → Nat,
      (∑ k, d k) ≤ N → (∑ k, e k) ≤ N →
      (∑ k, e k) < (∑ k, d k) →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (1 : Complex))) = 0)
    (hsame : ∀ d e : Fin n → Nat,
      (∑ k, d k) ≤ N → (∑ k, e k) ≤ N →
      (∑ k, e k) = (∑ k, d k) →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (1 : Complex))) =
            (if d = e then 1 else 0))
    (value : (Fin n → Nat) → Complex) :
    Exists fun Q : MvPolynomial (Fin n) Complex =>
      (e : Fin n → Nat) →
        (∑ k, e k) ≤ N →
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (MvPolynomial.aeval phi Q) = value e := by sorry
