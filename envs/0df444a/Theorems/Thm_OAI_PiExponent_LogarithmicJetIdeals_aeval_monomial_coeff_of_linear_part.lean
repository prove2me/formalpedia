-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_aeval_monomial_coeff_of_linear_part
-- name    : OAI.PiExponent.LogarithmicJetIdeals.aeval_monomial_coeff_of_linear_part
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T17:36:39.543991+00:00
-- url     : https://prove2.me/theorems/dee0bd1c-207f-4997-b722-3c93f20c5b92
-- title:
--   Low-degree coefficients of a substituted monomial
-- statement:
--   For a monomial with exponent `a`, substituting series whose constant and linear coefficients match the corresponding variables preserves every coefficient indexed by `e` whose total degree is at most the total degree of `a`. The argument uses the product structure of the substituted monomial and coefficient convolution.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.aeval_monomial_coeff_of_linear_part
    {m : Nat}
    (R : Fin (m + 1) -> MvPowerSeries (Fin (m + 1)) Complex)
    (a : Finsupp (Fin (m + 1)) Nat)
    (hR : ∀ (i : Fin (m + 1)) (d : Fin (m + 1) -> Nat),
      (∑ k : Fin (m + 1), d k) <= 1 ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (R i) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (MvPowerSeries.X i))
    (e : Fin (m + 1) -> Nat)
    (he : (∑ k : Fin (m + 1), e k) <= (∑ k : Fin (m + 1), a k)) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval R (MvPolynomial.monomial a (1 : Complex))) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.monomial a (1 : Complex)) := by sorry
