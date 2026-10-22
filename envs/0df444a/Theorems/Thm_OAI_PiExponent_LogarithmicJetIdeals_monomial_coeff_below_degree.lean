-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_monomial_coeff_below_degree
-- name    : OAI.PiExponent.LogarithmicJetIdeals.monomial_coeff_below_degree
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T17:59:42.212987+00:00
-- url     : https://prove2.me/theorems/67777b5c-41d6-47e1-9254-fd7553d37b5c
-- title:
--   Monomial coefficients vanish below the monomial degree
-- statement:
--   The coefficient of a monomial at any exponent function whose total degree is strictly below the monomial's degree is zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.monomial_coeff_below_degree
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    (a : Finsupp ι Nat)
    (e : ι -> Nat)
    (he : (∑ k : ι, e k) < (∑ k : ι, a k)) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.monomial a (1 : K)) = 0 := by sorry
