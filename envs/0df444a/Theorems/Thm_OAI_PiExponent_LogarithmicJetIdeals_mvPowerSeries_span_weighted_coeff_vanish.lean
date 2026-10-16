-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_mvPowerSeries_span_weighted_coeff_vanish
-- name    : OAI.PiExponent.LogarithmicJetIdeals.mvPowerSeries_span_weighted_coeff_vanish
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T06:55:29.947401+00:00
-- url     : https://prove2.me/theorems/cf456a17-70c4-485d-b4d5-a27ba9bfb695
-- title:
--   Weighted coefficient vanishing passes to a power-series ideal
-- statement:
--   For strictly positive coordinate weights, if every generator series has zero coefficients at all degrees below a strict weighted cutoff, every series in their ideal has zero coefficient at each degree below that cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.mvPowerSeries_span_weighted_coeff_vanish
    {m : ℕ} (ω : Fin (m + 1) → ℝ) (R : ℝ)
    (hω : ∀ j : Fin (m + 1), 0 < ω j)
    (S : Set (MvPowerSeries (Fin (m + 1)) ℂ))
    (hS : ∀ F ∈ S, ∀ b : Fin (m + 1) → ℕ,
      (∑ j, ω j * (b j : ℝ)) < R →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b) F = 0)
    (a : Fin (m + 1) → ℕ)
    (ha : (∑ j, ω j * (a j : ℝ)) < R)
    (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : F ∈ Ideal.span S) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) F = 0 := by sorry
