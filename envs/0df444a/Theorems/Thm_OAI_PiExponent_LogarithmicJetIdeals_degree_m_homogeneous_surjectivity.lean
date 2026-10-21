-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_degree_m_homogeneous_surjectivity
-- name    : OAI.PiExponent.LogarithmicJetIdeals.degree_m_homogeneous_surjectivity
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:33:33.670166+00:00
-- url     : https://prove2.me/theorems/7c70dcb9-8ef6-40e3-9e40-f859ded3c315
-- title:
--   Realize prescribed coefficients by a homogeneous correction
-- statement:
--   Under the triangular coefficient hypotheses through degree N, for any prescribed coefficients at degree m there is a polynomial correction whose evaluation has those coefficients at degree m and vanishes in every lower degree. Its role is the homogeneous correction step: take a finite linear combination of degree-m monomials and use the diagonal and lower-triangular hypotheses.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.degree_m_homogeneous_surjectivity
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
    (value : (Fin n → Nat) → Complex)
    (m : Nat)
    (hm : m ≤ N) :
    ∃ R : MvPolynomial (Fin n) Complex,
      (∀ e : Fin n → Nat, (∑ k, e k) < m →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi R) = 0) ∧
      (∀ e : Fin n → Nat, (∑ k, e k) = m →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi R) = value e) := by sorry
