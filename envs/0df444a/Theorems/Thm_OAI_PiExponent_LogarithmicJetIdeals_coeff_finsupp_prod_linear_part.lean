-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_finsupp_prod_linear_part
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_linear_part
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T17:58:34.439184+00:00
-- url     : https://prove2.me/theorems/c661c5c0-98dd-407f-a416-0e16dcbebe05
-- title:
--   Boundary coefficient depends only on linear parts
-- statement:
--   For a product with total factor count equal to the requested total degree, its coefficient is unchanged when every factor is replaced by the variable having the same constant and linear coefficients.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_linear_part
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    (R : ι -> MvPowerSeries ι K)
    (a : Finsupp ι Nat)
    (hR : ∀ (i : ι) (d : ι -> Nat),
      (∑ k : ι, d k) <= 1 ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (R i) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (MvPowerSeries.X i))
    (e : ι -> Nat)
    (he : (∑ k : ι, e k) = (∑ k : ι, a k)) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (a.prod fun i k => R i ^ k) =
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (a.prod fun i k => MvPowerSeries.X i ^ k) := by sorry
