-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_monomial_coeff
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_monomial_coeff
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T06:41:27.444934+00:00
-- url     : https://prove2.me/theorems/9a12e53c-8bc1-4944-bdc7-063fbb122f4e
-- title:
--   Coefficient of a weighted evaluated monomial
-- statement:
--   The coefficient of a weighted evaluated monomial is its weight when the queried multi-index equals the monomial's index, and zero otherwise, assuming the given lower-degree and equal-degree coefficient conditions through cutoff N. The non-strict degree bound allows both the strict-lower and equal-degree cases.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_monomial_coeff
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
    (c : Complex)
    (d e : Fin n → Nat)
    (hd : (∑ k, d k) ≤ N)
    (he : (∑ k, e k) ≤ N)
    (hle : (∑ k, e k) ≤ (∑ k, d k)) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval phi
        (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) c)) =
      (if d = e then c else 0) := by sorry
