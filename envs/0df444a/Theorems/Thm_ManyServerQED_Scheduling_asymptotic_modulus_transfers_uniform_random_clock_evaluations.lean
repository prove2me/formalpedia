-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_asymptotic_modulus_transfers_uniform_random_clock_evaluations
-- name    : ManyServerQED.Scheduling.asymptotic_modulus_transfers_uniform_random_clock_evaluations
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:13:19.923501+00:00
-- url     : https://prove2.me/theorems/f81c2a91-b0dc-4080-9ba8-503fa986adc8
-- title:
--   Uniform evaluation at nearby random clocks
-- statement:
--   Suppose a process sequence has an asymptotically small uniform modulus in probability on compact intervals. On a fixed interval, if two nonnegative random clocks differ by a quantity tending uniformly to zero in probability and one clock is bounded by the interval horizon, evaluation at the two clocks gives processes whose difference tends uniformly to zero in probability.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open Filter Topology Set MeasureTheory
open scoped ENNReal

theorem ManyServerQED.Scheduling.asymptotic_modulus_transfers_uniform_random_clock_evaluations {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E] (P : Measure Ω)
    (X : ℕ → Ω → ℝ → E)
    (h : ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ dist (X n ω s) (X n ω t)} ≤ ENNReal.ofReal η)
    (u v : ℕ → Ω → ℝ → ℝ) (T : ℝ)
    (hu : ∀ᶠ n in atTop, ∀ ω t, t ∈ Icc (0:ℝ) T → 0 ≤ u n ω t)
    (hv : ∀ᶠ n in atTop, ∀ ω t, t ∈ Icc (0:ℝ) T → v n ω t ∈ Icc (0:ℝ) T)
    (hUV : ∀ δ > (0:ℝ), Tendsto (fun n => P {ω | ∃ t ∈ Icc (0:ℝ) T,
      δ ≤ |u n ω t-v n ω t|}) atTop (𝓝 0)) :
    ∀ ε > (0:ℝ), Tendsto (fun n => P {ω | ∃ t ∈ Icc (0:ℝ) T,
      ε ≤ dist (X n ω (u n ω t)) (X n ω (v n ω t))}) atTop (𝓝 0) := by sorry
