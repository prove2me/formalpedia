-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_prod_zero_constant_below_degree
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coeff_prod_zero_constant_below_degree
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T17:59:12.624368+00:00
-- url     : https://prove2.me/theorems/a2521d15-2b67-49a5-8228-7d403370a05f
-- title:
--   Product coefficient vanishing from zero constant terms
-- statement:
--   For a finite family of multivariate power series with zero constant coefficients, every coefficient of their powered product vanishes below the total number of factors.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coeff_prod_zero_constant_below_degree
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    (R : ι -> MvPowerSeries ι K)
    (a : Finsupp ι Nat)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (R i) = 0)
    (e : ι -> Nat)
    (he : (∑ k : ι, e k) < (∑ k : ι, a k)) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (a.prod fun i k => R i ^ k) = 0 := by sorry
