-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_finite_dimensional_cadlag_processes_have_compact_subsequence_coupling
-- name    : ManyServerQED.Scheduling.finite_dimensional_cadlag_processes_have_compact_subsequence_coupling
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:10:45.955818+00:00
-- url     : https://prove2.me/theorems/eaa64943-9af1-455b-a46f-e7b9e2bbbf3d
-- title:
--   A locally uniform subsequence coupling for càdlàg processes
-- statement:
--   A finite-dimensional càdlàg sequence with measurable evaluations, asymptotically tight compact suprema, and a tight vanishing interval modulus has a subsequence with a continuous limit and a coupling converging locally uniformly almost surely.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_bounded_unit_process_subsequence_finite_observation_limit
import Theorems.Thm_ManyServerQED_Scheduling_weighted_arctangent_time_compression_transfers_modulus
import Theorems.Thm_ManyServerQED_Scheduling_functional_coupling_from_fdd_and_interval_modulus
import Theorems.Thm_ManyServerQED_Scheduling_arctangent_path_coupling_recovers_original_paths
import Theorems.Thm_ManyServerQED_Scheduling_arctangent_fdd_limit_is_interior_on_compact_rational_times
import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_Reiman84_QueueLength_Paths
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open BellWilliams2001.ThresholdPolicy Reiman84.QueueLength
open ManyServerQED.Scheduling

theorem ManyServerQED.Scheduling.finite_dimensional_cadlag_processes_have_compact_subsequence_coupling {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℕ} (X : ℕ → Ω → ℝ → Fin k → ℝ)
    (hX : ∀ n ω i, IsCadlag (fun t => X n ω t i))
    (hXm : ∀ n t, 0 ≤ t → Measurable (fun ω => X n ω t))
    (hB : ∀ (T : ℕ) (η : ℝ), 0 < η → ∃ A ≥ (0:ℝ), ∀ᶠ n in atTop,
      P {ω | ∃ t ∈ Icc (0:ℝ) (T:ℝ), A < ‖X n ω t‖} ≤ ENNReal.ofReal η)
    (hM : ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) :
    ∃ r : ℕ → ℕ, StrictMono r ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (x : Ω' → ℝ → Fin k → ℝ),
        IsProbabilityMeasure P' ∧ (∀ ω, ContinuousOn (x ω) (Ici (0:ℝ))) ∧
        (∀ t, 0 ≤ t → Measurable (fun ω => x ω t)) ∧
        CouplingConverges P P' (fun n => X (r n)) x := by sorry
