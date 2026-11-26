-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_arrival_norm_and_modulus_bounds
-- name    : ManyServerQED.Scheduling.queue_arrival_norm_and_modulus_bounds
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:39:26.607218+00:00
-- url     : https://prove2.me/theorems/24f9972c-9505-4358-a5db-5962df33d437
-- title:
--   Norm and modulus bounds for centered arrivals
-- statement:
--   On every compact interval, the scaled queue arrival process in each class is bounded in probability and has an asymptotically small uniform modulus of continuity.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_queue_zero_variance_arrivals_uniform_bound
import Theorems.Thm_ManyServerQED_Scheduling_queue_positive_variance_arrivals_uniform_walk_approximation
import Theorems.Thm_ManyServerQED_Scheduling_renewal_epoch_walk_donsker_and_zero_variance
import Theorems.Thm_ManyServerQED_Scheduling_weak_continuous_path_laws_control_norm_and_modulus
open Filter Topology Set MeasureTheory ProbabilityTheory DurrettProbability
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

theorem ManyServerQED.Scheduling.queue_arrival_norm_and_modulus_bounds {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {k : ℕ} (M : SystemSequence Ω k) (i : Fin k)
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {B : ℝ≥0 → Ω' → ℝ}
    (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous (fun t => B t ω))
    (T : ℝ) (hT : 0 ≤ T) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ A > 0, ∃ δ > 0, ∀ᶠ n in atTop,
      M.P {ω | (∃ t ∈ Icc (0:ℝ) T, A ≤ |M.Ahat n ω t i|) ∨
        ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T, |s-t| ≤ δ ∧
          ε ≤ |M.Ahat n ω s i-M.Ahat n ω t i|} ≤ ENNReal.ofReal η := by sorry
