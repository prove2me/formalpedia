-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_finsupp_prod_of_linear_part
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_of_linear_part
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T17:41:56.977387+00:00
-- url     : https://prove2.me/theorems/658bfa98-a7c3-4d8b-83cb-299f2a8d2ea1
-- title:
--   Coefficients of a product with prescribed linear parts
-- statement:
--   If each substituted series has the same constant and linear coefficients as its corresponding variable, then the product containing `a i` copies of each series agrees with the monomial `a` at every coefficient of total degree at most the total exponent sum. The finite product convolution forces every factor in a contributing summand to have degree one.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_of_linear_part
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
      (a.prod fun i k => R i ^ k) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.monomial a (1 : Complex)) := by sorry
