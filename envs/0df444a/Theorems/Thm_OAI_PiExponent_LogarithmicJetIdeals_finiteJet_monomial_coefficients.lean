-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finiteJet_monomial_coefficients
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finiteJet_monomial_coefficients
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:17:40.129264+00:00
-- url     : https://prove2.me/theorems/f0217965-8378-4615-b12a-2e28195d3718
-- title:
--   Leading coefficients of substituted monomials
-- statement:
--   For coordinates with zero constant term and identity linear coefficients, a substituted monomial has no coefficients below its total degree, and its coefficients in that same degree are those of the original monomial.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.finiteJet_monomial_coefficients
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (phi i) = 0)
    (hlinear : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (phi i) =
      (if i = j then 1 else 0))
    (d e : Fin n → Nat) :
    ((∑ k, e k) < (∑ k, d k) →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (1 : Complex))) = 0) ∧
    ((∑ k, e k) = (∑ k, d k) →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (1 : Complex))) =
            (if d = e then 1 else 0)) := by sorry
