-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_uniform_path_approximation_transfers_norm_and_modulus_bounds
-- name    : ManyServerQED.Scheduling.uniform_path_approximation_transfers_norm_and_modulus_bounds
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:39:02.140995+00:00
-- url     : https://prove2.me/theorems/a4b7d53c-aaf8-4c36-90c3-0896f545ad21
-- title:
--   Norm and modulus bounds from uniform path approximation
-- statement:
--   Suppose random continuous paths on the unit interval converge weakly. A real-valued process uniformly close in probability over a finite horizon to a fixed multiple of these paths evaluated on uniformly Lipschitz clocks has bounded sup norms in probability and an asymptotically small modulus of continuity.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_weak_continuous_path_laws_control_norm_and_modulus
open Filter Topology Set MeasureTheory ProbabilityTheory DurrettProbability
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

theorem ManyServerQED.Scheduling.uniform_path_approximation_transfers_norm_and_modulus_bounds {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Q : ℕ → Ω → ℝ → ℝ) (Y : ℕ → Ω → PathSpace) (Z : Ω' → PathSpace)
    (hY : TendstoInDistribution Y atTop Z (fun _ => P) P')
    (T c L : ℝ) (hL : 0 < L) (d : ℕ → ℝ → Set.Icc (0:ℝ) 1)
    (hD : ∀ᶠ n in atTop, ∀ s ∈ Icc (0:ℝ) T, ∀ t ∈ Icc (0:ℝ) T,
      dist (d n s) (d n t) ≤ L* |s-t|)
    (hApprox : ∀ ε > (0:ℝ), Tendsto (fun n => P {ω | ∃ t ∈ Icc (0:ℝ) T,
      ε ≤ |Q n ω t - c*Y n ω (d n t)|}) atTop (𝓝 0)) :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ A > 0, ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | (∃ t ∈ Icc (0:ℝ) T, A ≤ |Q n ω t|) ∨
        ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T, |s-t| ≤ δ ∧
          ε ≤ |Q n ω s-Q n ω t|} ≤ ENNReal.ofReal η := by sorry
