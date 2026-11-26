-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_bounded_continuous_unit_processes_have_tight_subsequence
-- name    : ManyServerQED.Scheduling.bounded_continuous_unit_processes_have_tight_subsequence
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:13:15.265505+00:00
-- url     : https://prove2.me/theorems/4a640dca-dbd1-5a72-b8ab-aaf95b40f699
-- title:
--   A weakly convergent subsequence for bounded continuous paths
-- statement:
--   For continuous random vector paths on the unit interval, assume a uniform deterministic bound on all paths and that the moduli of continuity are small in probability uniformly in the sequence index. Their laws then have a weakly convergent subsequence on the continuous path space.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem ManyServerQED.Scheduling.bounded_continuous_unit_processes_have_tight_subsequence {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℕ} [MeasurableSpace C(Icc (0:ℝ) 1, Fin k → ℝ)]
    [BorelSpace C(Icc (0:ℝ) 1, Fin k → ℝ)]
    (X : ℕ → Ω → C(Icc (0:ℝ) 1, Fin k → ℝ)) (hX : ∀ n, Measurable (X n))
    (A : ℝ) (hA : ∀ n ω t, ‖X n ω t‖ ≤ A)
    (hM : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ > 0, ∀ n,
      P {ω | ∃ s t : Icc (0:ℝ) 1, dist s t ≤ δ ∧ ε ≤ dist (X n ω s) (X n ω t)}
        ≤ ENNReal.ofReal η) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ μ : ProbabilityMeasure C(Icc (0:ℝ) 1,Fin k → ℝ),
      TendstoInDistribution (fun n => X (r n)) atTop
        (id : C(Icc (0:ℝ) 1,Fin k → ℝ) → C(Icc (0:ℝ) 1,Fin k → ℝ))
        (fun _ => P) (μ : Measure C(Icc (0:ℝ) 1,Fin k → ℝ)) := by sorry
