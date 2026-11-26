-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_observation_at_zero
-- name    : ManyServerQED.Scheduling.queue_hjb_observation_at_zero
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:10:26.456045+00:00
-- url     : https://prove2.me/theorems/8585684e-6664-55eb-8573-4f1abf7e8c88
-- title:
--   Initial joint HJB queue observation
-- statement:
--   The joint HJB observation at time zero is the deterministic initial scaled queue state together with zero noise, drift, accumulated cost and accumulated HJB gap.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Definitions.Def_ManyServerQED_Scheduling_Policy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_hjb_observation_at_zero {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (u0 : Fin k → ℝ) (f : (Fin k → ℝ) → ℝ)
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ) (X0 : ℕ → Fin k → ℕ)
    (n : ℕ) (hC : M.IsControlled n (X0 n) (X n) (Ψ n)) (ω : Ω) :
    queueHJBObservation M L γ u0 f X Ψ n ω 0 =
      Fin.append (Fin.append (Fin.append (M.Xhat0 n (X0 n)) 0) 0) ![0,0] := by sorry
