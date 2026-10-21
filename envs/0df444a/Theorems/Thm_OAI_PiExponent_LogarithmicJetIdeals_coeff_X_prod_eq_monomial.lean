-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_X_prod_eq_monomial
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coeff_X_prod_eq_monomial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T17:58:58.845265+00:00
-- url     : https://prove2.me/theorems/efa5e3af-cfaa-4ca5-b683-b7a2f36105c9
-- title:
--   Variable product coefficient equals monomial coefficient
-- statement:
--   For any exponent vector, the coefficient of the product of variable powers indexed by a finitely supported exponent is the corresponding coefficient of the polynomial monomial.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coeff_X_prod_eq_monomial
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    (a : Finsupp ι Nat)
    (e : ι -> Nat) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (a.prod fun i k => MvPowerSeries.X i ^ k) =
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.monomial a (1 : K)) := by sorry
