-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_homogeneous_substitution_coefficients
-- name    : OAI.PiExponent.LogarithmicJetIdeals.homogeneous_substitution_coefficients
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:25:46.323513+00:00
-- url     : https://prove2.me/theorems/35310424-e207-4beb-8187-e0a0a1da3605
-- title:
--   Coefficients of substituted homogeneous polynomials
-- statement:
--   For any polynomial whose supported monomials all have total degree D, substitution by power series with zero constant terms and identity linear coefficients gives zero coefficients below degree D, and preserves every coefficient in degree D.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.homogeneous_substitution_coefficients
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (phi i) = 0)
    (hlinear : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (phi i) =
      (if i = j then 1 else 0))
    (P : MvPolynomial (Fin n) Complex)
    (D : Nat)
    (hhom : ∀ m ∈ P.support, (∑ i, m i) = D)
    (e : Fin n → Nat) :
    ((∑ i, e i) < D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi P) = 0) ∧
    ((∑ i, e i) = D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi P) =
          MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) P) := by sorry
