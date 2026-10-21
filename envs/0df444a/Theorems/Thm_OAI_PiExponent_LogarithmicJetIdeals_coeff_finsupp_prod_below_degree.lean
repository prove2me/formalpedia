-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_finsupp_prod_below_degree
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_below_degree
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T17:52:28.07066+00:00
-- url     : https://prove2.me/theorems/efbb579a-041f-483b-9df5-2b9c4a5b6f5d
-- title:
--   Vanishing of product coefficients below the factor count
-- statement:
--   For a finite family of series with the prescribed constant and linear coefficients, every coefficient of the powered product below the total factor count vanishes, as does the corresponding monomial coefficient.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_below_degree
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    (R : ι -> MvPowerSeries ι K)
    (a : Finsupp ι Nat)
    (hR : ∀ (i : ι) (d : ι -> Nat),
      (∑ k : ι, d k) <= 1 ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (R i) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (MvPowerSeries.X i))
    (e : ι -> Nat)
    (he : (∑ k : ι, e k) < (∑ k : ι, a k)) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (a.prod fun i k => R i ^ k) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.monomial a (1 : K)) := by sorry
