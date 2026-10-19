-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_subst_support_witness
-- name    : OAI.PiExponent.LogarithmicJetIdeals.subst_support_witness
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T21:44:52.4994+00:00
-- url     : https://prove2.me/theorems/363e63ba-0745-448a-91d3-8b9176bce273
-- title:
--   Support witness for formal power series substitution
-- statement:
--   A nonzero coefficient after substitution has a nonzero input coefficient whose substituted monomial product also has a nonzero coefficient at the output exponent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.subst_support_witness
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (sigma : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (hsigma : ∀ i : Fin (m + 1), ∀ b : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff b (sigma i) ≠ 0 →
        q i ≤ ∑ j, q j * (b j : ℝ))
    (F : MvPowerSeries (Fin (m + 1)) ℂ) (a : Fin (m + 1) → ℕ)
    (ha : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (MvPowerSeries.subst sigma F) ≠ 0) :
    ∃ b : Fin (m + 1) → ℕ,
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b) F ≠ 0 ∧
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (∏ i, sigma i ^ b i) ≠ 0 := by sorry
