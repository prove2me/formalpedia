-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_prod_eq_of_first_jet_eq
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coeff_prod_eq_of_first_jet_eq
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T18:32:19.11371+00:00
-- url     : https://prove2.me/theorems/465b5b41-c247-4120-883c-4c98fe272112
-- title:
--   Finite product coefficients depend on first jets at the boundary degree
-- statement:
--   For two finite families of multivariate power series whose coefficients agree in total degrees zero and one, if every series in the second family has zero constant coefficient, then their product coefficients agree at any exponent whose total degree is the number of factors. The degree-zero agreement also forces the first family’s constant coefficients to vanish.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coeff_prod_eq_of_first_jet_eq
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    {σ : Type} [Fintype σ]
    (A B : σ → MvPowerSeries ι K)
    (hAB : ∀ (j : σ) (d : ι → Nat),
      (∑ k : ι, d k) ≤ 1 →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (A j) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (B j))
    (hBzero : ∀ j : σ,
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (fun _ : ι => 0)) (B j) = 0)
    (e : ι → Nat)
    (he : (∑ k : ι, e k) = Fintype.card σ) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (∏ j : σ, A j) =
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (∏ j : σ, B j) := by sorry
