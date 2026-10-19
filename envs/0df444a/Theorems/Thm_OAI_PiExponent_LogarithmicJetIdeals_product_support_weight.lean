-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_product_support_weight
-- name    : OAI.PiExponent.LogarithmicJetIdeals.product_support_weight
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T21:45:27.829244+00:00
-- url     : https://prove2.me/theorems/b7981969-0e8c-4d6e-8f66-3e125ead5682
-- title:
--   Weighted support bound for products of substituted monomials
-- statement:
--   If the product of the substituted series powers has a nonzero coefficient at the output exponent, the output weighted degree is at least the input monomial's weighted degree.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.product_support_weight
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (sigma : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (hsigma : ∀ i : Fin (m + 1), ∀ b : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff b (sigma i) ≠ 0 →
        q i ≤ ∑ j, q j * (b j : ℝ))
    (b a : Fin (m + 1) → ℕ)
    (hprod : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (∏ i, sigma i ^ b i) ≠ 0) :
    (∑ j, q j * (b j : ℝ)) ≤ ∑ j, q j * (a j : ℝ) := by sorry
