-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_finsupp_prod_linear_part_finite
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_linear_part_finite
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T18:19:57.626446+00:00
-- url     : https://prove2.me/theorems/d9c4fd34-0f39-4b62-a660-e91a56448924
-- title:
--   Boundary coefficient for finite products of linear parts
-- statement:
--   For a finite family of multivariate power series, the coefficient of their product at total degree equal to the number of factors agrees with the corresponding coefficient of the product of assigned variables, provided each series and its assigned variable have the same coefficients in degrees zero and one. The empty-family case is included.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_linear_part_finite
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    {σ : Type} [Fintype σ]
    (R : σ -> MvPowerSeries ι K)
    (v : σ -> ι)
    (hR : ∀ (j : σ) (d : ι -> Nat),
      (∑ k : ι, d k) <= 1 ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (R j) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (MvPowerSeries.X (v j)))
    (e : ι -> Nat)
    (he : (∑ k : ι, e k) = Fintype.card σ) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (∏ j : σ, R j) =
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (∏ j : σ, MvPowerSeries.X (v j)) := by sorry
