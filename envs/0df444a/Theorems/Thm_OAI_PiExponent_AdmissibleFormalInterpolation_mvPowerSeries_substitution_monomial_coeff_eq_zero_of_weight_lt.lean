-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_mvPowerSeries_substitution_monomial_coeff_eq_zero_of_weight_lt
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.mvPowerSeries_substitution_monomial_coeff_eq_zero_of_weight_lt
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-18T02:19:14.135321+00:00
-- url     : https://prove2.me/theorems/9af9edc3-4dd6-46fa-920c-d21ee3c48382
-- title:
--   Filtered substitution cannot lower monomial weight
-- statement:
--   For any real coordinate weights, replacing each variable Xᵢ₊₁ by Xᵢ₊₁+Lᵢ cannot create a monomial coefficient at strictly lower weight if every coefficient of Lᵢ has weight at least uᵢ. This applies also when some weights are nonpositive; the assertion follows by expanding the finite monomial substitution and checking the weight of each contribution.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedJetShear

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.mvPowerSeries_substitution_monomial_coeff_eq_zero_of_weight_lt
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ)
    (L : Fin m → MvPowerSeries (Fin (m + 1)) ℂ)
    (hL : ∀ i α,
      (∑ j, Fin.cases v0 u j * (α j : ℝ)) < u i →
        MvPowerSeries.coeff α (L i) = 0)
    (a b : Fin (m + 1) → ℕ)
    (hab : (∑ i, Fin.cases v0 u i * (b i : ℝ)) <
      (∑ i, Fin.cases v0 u i * (a i : ℝ))) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (MvPolynomial.aeval (Fin.cases (MvPowerSeries.X 0)
        (fun i => MvPowerSeries.X i.succ + L i))
        (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) = 0 := by sorry
