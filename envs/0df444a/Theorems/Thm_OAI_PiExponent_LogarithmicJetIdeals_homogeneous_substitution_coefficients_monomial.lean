-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_homogeneous_substitution_coefficients_monomial
-- name    : OAI.PiExponent.LogarithmicJetIdeals.homogeneous_substitution_coefficients_monomial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:28:10.479715+00:00
-- url     : https://prove2.me/theorems/43418e39-9810-4563-8f52-19c1f7eddc85
-- title:
--   Coefficients after substituting into a monomial
-- statement:
--   For a monomial of total degree D, substitution by power series with zero constant terms and identity linear coefficients gives no terms below degree D and preserves its coefficients in degree D.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.homogeneous_substitution_coefficients_monomial
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
        (MvPolynomial.aeval phi (MvPolynomial.monomial m c)) = 0) ∧
    ((∑ i, e i) = D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi (MvPolynomial.monomial m c)) =
          MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
            (MvPolynomial.monomial m c)) := by sorry
