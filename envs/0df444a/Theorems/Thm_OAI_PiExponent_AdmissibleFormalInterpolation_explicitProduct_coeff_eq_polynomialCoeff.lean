-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_explicitProduct_coeff_eq_polynomialCoeff
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.explicitProduct_coeff_eq_polynomialCoeff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T16:44:07.195123+00:00
-- url     : https://prove2.me/theorems/24b93c1d-05d8-430f-9470-54ef34e1328e
-- title:
--   Formal product coefficients match polynomial interpolation coefficients
-- statement:
--   The coefficient of the explicit multivariate formal-series product, at distinguished degree s and remaining degrees b, equals the coefficient of degree s in the polynomial coefficient at b of the interpolation monomial image.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.explicitProduct_coeff_eq_polynomialCoeff
    {m : ℕ} (j s : ℕ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (h : ℕ) (a b : Fin m → ℕ) :
  MvPowerSeries.coeff (InterpolationMatrix.exponentVector (Fin.cases s b))
      ((1 + MvPowerSeries.X 0) ^ h *
        ∏ i, (MvPowerSeries.C ((j : ℂ) * r i) + MvPowerSeries.X i.succ +
          liftLogSeries m (G i : PowerSeries ℂ)) ^ a i) =
    ((InterpolationMatrix.monomialImage r G j h a).coeff
      (InterpolationMatrix.exponentVector b)).coeff s := by sorry
