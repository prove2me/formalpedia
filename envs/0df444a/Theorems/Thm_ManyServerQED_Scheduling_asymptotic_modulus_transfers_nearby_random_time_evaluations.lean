-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_asymptotic_modulus_transfers_nearby_random_time_evaluations
-- name    : ManyServerQED.Scheduling.asymptotic_modulus_transfers_nearby_random_time_evaluations
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:55:41.68152+00:00
-- url     : https://prove2.me/theorems/c2687d53-b47e-4371-b7ac-0728f5877938
-- title:
--   Evaluation at nearby random times
-- statement:
--   Suppose a process sequence has an asymptotically small uniform modulus in probability on compact intervals. If two nonnegative random times differ by a term converging to zero in probability and one is uniformly bounded, then the two evaluations differ by a term converging to zero in probability.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open Filter Topology Set MeasureTheory
open scoped ENNReal

theorem ManyServerQED.Scheduling.asymptotic_modulus_transfers_nearby_random_time_evaluations {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E] (P : Measure Ω)
    (X : ℕ → Ω → ℝ → E)
    (h : ∀ (T : ℝ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T, |s-t| ≤ δ ∧
        ε ≤ dist (X n ω s) (X n ω t)} ≤ ENNReal.ofReal η)
    (u v : ℕ → Ω → ℝ) (T : ℝ)
    (hu : ∀ n ω, 0 ≤ u n ω) (hv : ∀ n ω, v n ω ∈ Icc (0:ℝ) T)
    (hUV : ∀ δ > (0:ℝ), Tendsto (fun n => P {ω | δ ≤ |u n ω-v n ω|}) atTop (𝓝 0)) :
    ∀ ε > (0:ℝ), Tendsto (fun n => P {ω | ε ≤ dist (X n ω (u n ω)) (X n ω (v n ω))})
      atTop (𝓝 0) := by sorry
