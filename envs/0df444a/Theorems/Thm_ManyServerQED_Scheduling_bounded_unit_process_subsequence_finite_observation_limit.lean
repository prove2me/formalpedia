-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_bounded_unit_process_subsequence_finite_observation_limit
-- name    : ManyServerQED.Scheduling.bounded_unit_process_subsequence_finite_observation_limit
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:53:04.354893+00:00
-- url     : https://prove2.me/theorems/554e51b2-0ea7-49f1-887e-98f8b2259786
-- title:
--   Continuous finite-observation limits for bounded unit processes
-- statement:
--   For real finite-vector processes bounded on the unit interval, an asymptotically small uniform modulus in probability gives a subsequence whose finite-dimensional laws converge to the evaluations of one continuous random path.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_bounded_continuous_unit_processes_have_tight_subsequence
import Theorems.Thm_ManyServerQED_Scheduling_eventual_continuous_modulus_bound_can_be_made_uniform
import Theorems.Thm_ManyServerQED_Scheduling_measurable_polygonal_approximation_on_unit_interval
open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

theorem ManyServerQED.Scheduling.bounded_unit_process_subsequence_finite_observation_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℕ} [MeasurableSpace C(Icc (0:ℝ) 1, Fin k → ℝ)] [BorelSpace C(Icc (0:ℝ) 1, Fin k → ℝ)]
    (X : ℕ → Ω → ℝ → Fin k → ℝ)
    (hX : ∀ n t, t ∈ Icc (0:ℝ) 1 → Measurable (fun ω => X n ω t))
    (A : ℝ) (hA : ∀ n ω t, t ∈ Icc (0:ℝ) 1 → ‖X n ω t‖ ≤ A)
    (hM : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) 1, ∃ t ∈ Icc (0:ℝ) 1, |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ μ : ProbabilityMeasure C(Icc (0:ℝ) 1, Fin k → ℝ),
      ∀ (m : ℕ) (τ : Fin m → Icc (0:ℝ) 1),
        TendstoInDistribution (fun n ω j => X (r n) ω (τ j)) atTop
          (fun (p : C(Icc (0:ℝ) 1, Fin k → ℝ)) j => p (τ j))
          (fun _ => P) (μ : Measure C(Icc (0:ℝ) 1, Fin k → ℝ)) := by sorry
