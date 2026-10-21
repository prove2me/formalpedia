-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_degree_m_correction
-- name    : OAI.PiExponent.LogarithmicJetIdeals.degree_m_correction
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:30:20.241027+00:00
-- url     : https://prove2.me/theorems/34062fc8-28a1-4322-8eb5-9f9c3ee7ad5b
-- title:
--   Correct coefficients at one homogeneous degree
-- statement:
--   Under the triangular coefficient hypotheses through degree N, for any polynomial Q and requested coefficient function, there is a correction polynomial R such that adding R preserves every coefficient below degree m and sets every coefficient of degree m to its requested value.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.degree_m_correction
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
    (Q : MvPolynomial (Fin n) Complex)
    (hm : m ≤ N) :
    ∃ R : MvPolynomial (Fin n) Complex,
      (∀ e : Fin n → Nat, (∑ k, e k) < m →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi (Q + R)) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi Q)) ∧
      (∀ e : Fin n → Nat, (∑ k, e k) = m →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi (Q + R)) = value e) := by sorry
