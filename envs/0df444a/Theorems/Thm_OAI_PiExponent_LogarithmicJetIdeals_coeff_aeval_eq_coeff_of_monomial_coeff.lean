-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_aeval_eq_coeff_of_monomial_coeff
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coeff_aeval_eq_coeff_of_monomial_coeff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T17:37:09.811356+00:00
-- url     : https://prove2.me/theorems/20b1d668-b5aa-4a7b-8531-d8df54e84940
-- title:
--   Coefficient transfer from supported monomials
-- statement:
--   If evaluation preserves the coefficient indexed by `e` for every unit monomial supported in `Q`, then it preserves that coefficient for `Q`. This is the finite polynomial expansion step, using additivity of evaluation and coefficient extraction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coeff_aeval_eq_coeff_of_monomial_coeff
    {m : Nat}
    (R : Fin (m + 1) -> MvPowerSeries (Fin (m + 1)) Complex)
    (Q : MvPolynomial (Fin (m + 1)) Complex)
    (e : Fin (m + 1) -> Nat)
    (hmono : ∀ a : Finsupp (Fin (m + 1)) Nat, a ∈ Q.support ->
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval R (MvPolynomial.monomial a (1 : Complex))) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.monomial a (1 : Complex))) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval R Q) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) Q := by sorry
