-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_mvPowerSeries_aeval_monomial_coeff_eq_zero_of_weight_lt
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.mvPowerSeries_aeval_monomial_coeff_eq_zero_of_weight_lt
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T07:29:51.494865+00:00
-- url     : https://prove2.me/theorems/48884df3-45a9-4fcb-aaa3-70774376f3d6
-- title:
--   Weighted support is preserved by monomial substitution
-- statement:
--   For any finite family of multivariate formal power series whose coefficients are supported at weights at least their assigned variable weights, evaluating a monomial in that family cannot produce a coefficient of strictly lower total weight.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedJetShear

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.mvPowerSeries_aeval_monomial_coeff_eq_zero_of_weight_lt
    {n : ℕ} (w : Fin n → ℝ)
    (F : Fin n → MvPowerSeries (Fin n) ℂ)
    (hF : ∀ (i : Fin n) (α : Fin n →₀ ℕ),
      (∑ j, w j * (α j : ℝ)) < w i →
        MvPowerSeries.coeff α (F i) = 0)
    (a b : Fin n → ℕ)
    (hab : (∑ i, w i * (b i : ℝ)) <
      (∑ i, w i * (a i : ℝ))) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (MvPolynomial.aeval F
        (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) = 0 := by sorry
