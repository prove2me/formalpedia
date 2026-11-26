-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_observation_rows_are_cadlag
-- name    : ManyServerQED.Scheduling.queue_hjb_observation_rows_are_cadlag
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:31:57.503156+00:00
-- url     : https://prove2.me/theorems/722fa8c0-162b-4a04-8738-0668ec4db62f
-- title:
--   Joint queue HJB observations are càdlàg
-- statement:
--   For every positive row index the controlled state, normalized noise, accumulated drift, running cost and HJB gap together form a coordinatewise càdlàg process.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_row_integral_paths
import Theorems.Thm_ManyServerQED_Scheduling_controlled_queue_state_and_effective_noise_are_cadlag
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_hjb_observation_rows_are_cadlag {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (γ ϱ mL : ℝ) (hA2 : Assumption2 Lt ϱ mL)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (f : (Fin k → ℝ) → ℝ) (hH : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ) (X0 : ℕ → Fin k → ℕ)
    (hC : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n)) :
    ∀ n, 1 ≤ n → ∀ ω i, IsCadlag (fun t =>
      queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ n ω t i) := by sorry
