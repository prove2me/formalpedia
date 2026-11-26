-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_continuous_adapted_capped_exit_localization
-- name    : ManyServerQED.Scheduling.continuous_adapted_capped_exit_localization
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:52:09.326531+00:00
-- url     : https://prove2.me/theorems/e2eb438e-d49a-41ed-9c4b-103d8921e6a4
-- title:
--   Bounded localization for a continuous adapted process
-- statement:
--   For a continuous adapted process and a fixed finite time horizon, consider its first strict exit from each increasing sequence of norm balls, capped at the horizon. A strict comparison of an exit time with a deterministic time is measurable in the information at that deterministic time. The exit times increase and are eventually equal to the horizon on each path. Up to and including the exit time the norm is bounded by the localization radius if it starts inside the ball.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem ManyServerQED.Scheduling.continuous_adapted_capped_exit_localization
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (F : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → E) (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω, Continuous (fun t => X t ω)) (T : ℝ≥0) (r : ℝ) :
    ∃ τ : ℕ → Ω → ℝ≥0,
      (∀ (R : ℕ) (a : ℝ≥0), MeasurableSet[F a] {ω | τ R ω < a}) ∧
      (∀ R ω, τ R ω ≤ T) ∧
      (∀ ω, Monotone (fun R => τ R ω)) ∧
      (∀ ω, ∀ᶠ R in atTop, τ R ω = T) ∧
      (∀ R ω t, t < τ R ω → ‖X t ω‖ ≤ r+R) ∧
      (∀ (R : ℕ) ω, ‖X 0 ω‖ ≤ r+R → ‖X (τ R ω) ω‖ ≤ r+R) := by sorry
