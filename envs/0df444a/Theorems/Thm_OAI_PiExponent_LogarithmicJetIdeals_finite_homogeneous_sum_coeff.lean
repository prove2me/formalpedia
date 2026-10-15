-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_homogeneous_sum_coeff
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finite_homogeneous_sum_coeff
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T06:36:26.713201+00:00
-- url     : https://prove2.me/theorems/9972c3dc-5b9e-485d-b289-8b6a67230239
-- title:
--   Coefficients of the evaluated homogeneous sum
-- statement:
--   For a finite set containing exactly the degree-$m$ multi-indices, the coefficient at any degree at most $m$ of the evaluated weighted sum is the prescribed value in degree $m$ and zero below it. The lower-degree and equal-degree cases use `hbelow` and `hsame`, respectively.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.finite_homogeneous_sum_coeff
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
    (hm : m ≤ N)
    (S : Finset (Fin n → Nat))
    (hS : ∀ d : Fin n → Nat, d ∈ S ↔ (∑ k, d k) = m)
    (e : Fin n → Nat)
    (he : (∑ k, e k) ≤ m) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval phi
        (∑ d ∈ S,
          MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (value d))) =
      (if (∑ k, e k) = m then value e else 0) := by sorry
