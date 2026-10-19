-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_generic_product_support_weight
-- name    : OAI.PiExponent.LogarithmicJetIdeals.generic_product_support_weight
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T22:00:00.781993+00:00
-- url     : https://prove2.me/theorems/4390c994-06a3-4690-82b7-922b1a7b6edc
-- title:
--   Weighted support bound for products of powers of multivariate power series
-- statement:
--   For any finite family of multivariate power series, if each supported exponent in the ith series has weighted degree at least q i, then every exponent supported in the product of the series raised to natural-number multiplicities has weighted degree at least the weighted sum of those multiplicities.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.generic_product_support_weight
    {n : ℕ} (q : Fin n → ℝ)
    (sigma : Fin n → MvPowerSeries (Fin n) ℂ)
    (hsigma : ∀ i : Fin n, ∀ c : Fin n →₀ ℕ,
      MvPowerSeries.coeff c (sigma i) ≠ 0 →
        q i ≤ ∑ j, q j * (c j : ℝ))
    (b : Fin n → ℕ) (e : Fin n →₀ ℕ)
    (hprod : MvPowerSeries.coeff e (∏ i, sigma i ^ b i) ≠ 0) :
    (∑ j, q j * (b j : ℝ)) ≤ ∑ j, q j * (e j : ℝ) := by sorry
