-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_interval_modulus_and_initial_bound_give_compact_containment
-- name    : ManyServerQED.Scheduling.interval_modulus_and_initial_bound_give_compact_containment
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:10:23.471005+00:00
-- url     : https://prove2.me/theorems/68eb93d3-789c-4501-a101-751489251f18
-- title:
--   Compact containment from an initial bound and an interval modulus
-- statement:
--   For a sequence of paths uniformly bounded at time zero, an asymptotic interval modulus bound implies an asymptotic compact-containment bound on the given horizon.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

theorem ManyServerQED.Scheduling.interval_modulus_and_initial_bound_give_compact_containment {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (X : ℕ → Ω → ℝ → E) (T : ℝ) (hT : 0 ≤ T)
    (C : ℝ) (hC : 0 ≤ C) (h0 : ∀ᶠ n in atTop, ∀ ω, ‖X n ω 0‖ ≤ C)
    (hM : ∀ η : ℝ, 0 < η → ∃ δ > (0:ℝ), ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T, |s-t| ≤ δ ∧
        1 ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) :
    ∀ η : ℝ, 0 < η → ∃ A ≥ (0:ℝ), ∀ᶠ n in atTop,
      P {ω | ∃ t ∈ Icc (0:ℝ) T, A < ‖X n ω t‖} ≤ ENNReal.ofReal η := by sorry
