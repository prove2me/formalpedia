-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coefficients_scaled_product_identity_linear
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coefficients_scaled_product_identity_linear
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:30:59.386491+00:00
-- url     : https://prove2.me/theorems/e60415a1-a0c5-452b-a0ec-1bc4ca25c2e9
-- title:
--   Initial coefficients of a scaled product of substituted coordinate powers
-- statement:
--   For coordinate power series with zero constant coefficients and identity linear coefficients, the scaled product of their powers has no coefficients below the total degree of the exponent vector, and its coefficients at that degree agree with the corresponding monomial.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coefficients_scaled_product_identity_linear
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (phi i) = 0)
    (hlinear : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (phi i) =
      (if i = j then 1 else 0))
    (m : Fin n →₀ Nat)
    (c : Complex)
    (D : Nat)
    (e : Fin n → Nat)
    (hdeg : (∑ i, m i) = D) :
    ((∑ i, e i) < D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        ((algebraMap Complex (MvPowerSeries (Fin n) Complex) c) *
          m.prod (fun i k => phi i ^ k)) = 0) ∧
    ((∑ i, e i) = D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        ((algebraMap Complex (MvPowerSeries (Fin n) Complex) c) *
          m.prod (fun i k => phi i ^ k)) =
          MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
            (MvPolynomial.monomial m c)) := by sorry
