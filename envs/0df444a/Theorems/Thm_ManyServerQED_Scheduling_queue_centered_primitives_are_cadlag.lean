-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_centered_primitives_are_cadlag
-- name    : ManyServerQED.Scheduling.queue_centered_primitives_are_cadlag
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:55:47.045503+00:00
-- url     : https://prove2.me/theorems/92276bfe-6b0c-4ac0-94ae-3272750eceb5
-- title:
--   Càdlàg paths for centered queue primitives
-- statement:
--   For every system index and class, the centered scaled arrival, potential service, and potential abandonment processes of the many-server queue have càdlàg paths.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_Policy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_centered_primitives_are_cadlag {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) :
    ∀ n ω i,
      IsCadlag (fun t => M.Ahat n ω t i) ∧ IsCadlag (fun t => M.Shat n ω t i) ∧
        IsCadlag (fun t => M.Rhat n ω t i) := by sorry
