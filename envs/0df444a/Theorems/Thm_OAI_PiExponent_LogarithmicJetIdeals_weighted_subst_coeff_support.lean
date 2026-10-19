-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_subst_coeff_support
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_subst_coeff_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T21:39:52.720795+00:00
-- url     : https://prove2.me/theorems/4828dca3-6cf3-4fef-8a23-b8a4264410a9
-- title:
--   Weighted support under formal power series substitution
-- statement:
--   If a coefficient of a substituted series is nonzero, some nonzero input coefficient contributes at a weighted degree no greater than the output coefficient's weighted degree.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_subst_coeff_support
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (sigma : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (hsigma : ∀ i : Fin (m + 1), ∀ b : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff b (sigma i) ≠ 0 →
        q i ≤ ∑ j, q j * (b j : ℝ))
    (F : MvPowerSeries (Fin (m + 1)) ℂ) :
    ∀ a : Fin (m + 1) → ℕ,
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (MvPowerSeries.subst sigma F) ≠ 0 →
      ∃ b : Fin (m + 1) → ℕ,
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector b) F ≠ 0 ∧
        (∑ j, q j * (b j : ℝ)) ≤ ∑ j, q j * (a j : ℝ) := by sorry
