-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weighted_vanishing_subst_of_weight_support
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weighted_vanishing_subst_of_weight_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:46:41.56849+00:00
-- url     : https://prove2.me/theorems/81524d1e-e397-40de-bd06-8d8f7eaae0a9
-- title:
--   Weighted support bounds preserve coefficient vanishing under substitution
-- statement:
--   If all weights are positive and each substituted variable has coefficient support only at exponents whose weighted degree is at least that variable’s weight, then substitution preserves vanishing below any weighted threshold.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Substitution

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weighted_vanishing_subst_of_weight_support
    {m : ℕ} (q : Fin (m + 1) → ℝ)
    (φ : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (hq : ∀ i, 0 < q i)
    (hφ : ∀ (i : Fin (m + 1)) (a : Fin (m + 1) → ℕ),
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) (φ i) ≠ 0 →
      q i ≤ ∑ j, q j * (a j : ℝ))
    (H : ℝ) (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : ∀ a : Fin (m + 1) → ℕ,
      (∑ i, q i * (a i : ℝ)) < H →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) F = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ i, q i * (a i : ℝ)) < H →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (MvPowerSeries.subst φ F) = 0 := by sorry
