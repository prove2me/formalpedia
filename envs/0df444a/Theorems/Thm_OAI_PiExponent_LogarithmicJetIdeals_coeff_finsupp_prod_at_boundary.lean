-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_finsupp_prod_at_boundary
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_at_boundary
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T17:52:51.316829+00:00
-- url     : https://prove2.me/theorems/2ed856f7-13cb-43e3-958b-758d3e8a860f
-- title:
--   Product coefficients at the factor-count boundary
-- statement:
--   At total degree equal to the number of factors, the coefficient of the powered product is determined by the prescribed linear parts and agrees with the corresponding monomial coefficient.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_at_boundary
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
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.monomial a (1 : K)) := by sorry
