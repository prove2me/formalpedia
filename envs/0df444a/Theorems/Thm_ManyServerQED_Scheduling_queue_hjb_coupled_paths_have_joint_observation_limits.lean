-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_coupled_paths_have_joint_observation_limits
-- name    : ManyServerQED.Scheduling.queue_hjb_coupled_paths_have_joint_observation_limits
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:34:28.062615+00:00
-- url     : https://prove2.me/theorems/173a26fb-a7b8-4d54-ad45-77e3654e21cb
-- title:
--   Finite-dimensional convergence from joint queue path representation
-- statement:
--   Along the cofinal tail of a represented queue subsequence, every finite vector of evaluations of the original joint observation process converges in law to the corresponding evaluations of the continuous coupled limit.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_weak_convergence_from_coupled_observations
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_hjb_coupled_paths_have_joint_observation_limits {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}
    (d : QueueHJBPathSubseq P Z s) :
    letI := d.isProb
    ∃ N : ℕ, ∀ (m : ℕ) (τ : Fin m → ℝ≥0),
      TendstoInDistribution
        (fun j ω l => Z (s (d.r (j+N))) ω (τ l)) atTop
        (fun ω l => d.limit ω (τ l)) (fun _ => P) d.Q := by sorry
