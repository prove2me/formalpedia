-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_subst_preserves_filtered_vanishing
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_subst_preserves_filtered_vanishing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T19:23:02.333061+00:00
-- url     : https://prove2.me/theorems/ebef53be-42d5-4f72-979b-a683ec9848e0
-- title:
--   Weighted substitution preserves filtered vanishing
-- statement:
--   For strictly positive coordinate weights, a substitution whose coordinate monomials have at least their assigned weights preserves coefficient vanishing below any strict weighted cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_subst_preserves_filtered_vanishing
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (sigma : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (hsigma : ∀ i : Fin (m + 1), ∀ b : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff b (sigma i) ≠ 0 →
        q i ≤ ∑ j, q j * (b j : ℝ))
    (B : ℝ) (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) F = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (MvPowerSeries.subst sigma F) = 0 := by sorry
