-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaLaplacePositiveTimeAE
-- name    : Kyprianou.Ch01.gammaLaplacePositiveTimeAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T19:46:37.752024+00:00
-- url     : https://prove2.me/theorems/77602fac-4726-426d-80b6-26edf75f0cee
-- title:
--   Gamma-Laplace marginal is almost surely positive at every positive fixed time
-- statement:
--   At any fixed positive elapsed time, the gamma-subordinator marginal has strictly positive values almost surely. Apply the Markov bound μ{X_t≤0}≤E exp(−q X_t)=(α/(α+q))^(βt), then send q→+∞. No path assumptions, finite moments or additional distributions are required. This lemma discharges the fixed-time increment positivity step for strict monotonicity by Lévy stationarity.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.4, gamma process marginal positivity and strict increase.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.gammaLaplacePositiveTimeAE
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 < beta)
    (hLaplace : ∀ (t : ℝ≥0) (q : ℝ), 0 ≤ q →
      Integrable (fun ω => Real.exp (-q * X t ω)) P ∧
      (∫ ω, Real.exp (-q * X t ω) ∂P) =
        (alpha / (alpha + q)) ^ (beta * (t : ℝ))) :
    ∀ t : ℝ≥0, 0 < t → ∀ᵐ ω ∂P, 0 < X t ω := by sorry
