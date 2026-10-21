-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_seriesShear_monomial_coeff_eq_zero_of_weight_lt
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.seriesShear_monomial_coeff_eq_zero_of_weight_lt
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T22:20:11.589365+00:00
-- url     : https://prove2.me/theorems/5f6130c2-e864-4a74-8aa3-6cf8e366a800
-- title:
--   Polynomial shear cannot lower monomial weight
-- statement:
--   Under positive weights, the vanishing and weight bounds on D imply that a sheared monomial has no coefficient of strictly smaller weighted degree. Equality of weights is permitted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedJetShear

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.seriesShear_monomial_coeff_eq_zero_of_weight_lt
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ)
    (N : Fin m → ℕ) (D : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hD : ∀ i n, n < N i → PowerSeries.coeff n (D i) = 0)
    (a b : Fin (m + 1) → ℕ)
    (hab : (∑ i, Fin.cases v0 u i * (b i : ℝ)) <
      (∑ i, Fin.cases v0 u i * (a i : ℝ))) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (seriesShear D
        (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) = 0 := by sorry
