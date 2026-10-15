-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finiteJet_degree_extension
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finiteJet_degree_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T06:26:00.244705+00:00
-- url     : https://prove2.me/theorems/db8dc84d-87f2-4ea9-8f4d-b1b98c212b68
-- title:
--   Extend a finite jet interpolation by one degree
-- statement:
--   If a polynomial matches the desired coefficients below degree m and m is at most N, it can be adjusted to match all coefficients strictly below m+1 while preserving the lower-degree matches.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.finiteJet_degree_extension
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
    (hQ : ∀ e : Fin n → Nat, (∑ k, e k) < m →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi Q) = value e)
    (hm : m ≤ N) :
    ∃ Q' : MvPolynomial (Fin n) Complex,
      ∀ e : Fin n → Nat, (∑ k, e k) < m + 1 →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi Q') = value e := by sorry
