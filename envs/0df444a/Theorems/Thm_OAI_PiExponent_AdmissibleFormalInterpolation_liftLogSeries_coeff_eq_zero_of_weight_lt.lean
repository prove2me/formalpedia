-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_coeff_eq_zero_of_weight_lt
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_coeff_eq_zero_of_weight_lt
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:18:47.386979+00:00
-- url     : https://prove2.me/theorems/e123beb4-12e1-4669-9dda-44f87d7baed6
-- title:
--   Lifted series have no coefficients below the replacement weight
-- statement:
--   A lifted one-variable series has no coefficient of weighted degree below the replacement-coordinate weight when the original series vanishes below degree Nᵢ and Nᵢv₀ is at least uᵢ. The lift is supported only on coordinate zero; for a supported exponent, the strict weight bound implies its coordinate-zero degree is below Nᵢ.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedJetShear

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_coeff_eq_zero_of_weight_lt
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ)
    (N : Fin m → ℕ) (D : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hD : ∀ i n, n < N i → PowerSeries.coeff n (D i) = 0)
    (i : Fin m) (α : Fin (m + 1) →₀ ℕ)
    (hα : (∑ j, Fin.cases v0 u j * (α j : ℝ)) < u i) :
    MvPowerSeries.coeff α (liftLogSeries m (D i)) = 0 := by sorry
