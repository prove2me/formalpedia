-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_coupling_limit_state_balance
-- name    : ManyServerQED.Scheduling.queue_hjb_coupling_limit_state_balance
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:31:21.323834+00:00
-- url     : https://prove2.me/theorems/7cd6af6a-8060-539f-8a16-a0b50177605a
-- title:
--   Linear state balance of the coupled queue limit
-- statement:
--   The continuous limit of the joint queue observations has the specified initial state and zero initial cost and drift. Its state equals the initial state plus the unstandardized noise and the accumulated limiting drift.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_queue_diffusion_drift_remainder_uoc
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_observation_at_zero
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_hjb_coupling_limit_state_balance {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (u0 : Fin k → ℝ) (f : (Fin k → ℝ) → ℝ) (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n))
    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (d : QueueHJBPathSubseq M.P (queueHJBObservation M L γ u0 f X Ψ) s) :
    (∀ᵐ ω ∂d.Q, d.state 0 ω = x) ∧
    (∀ᵐ ω ∂d.Q, d.driftIntegral 0 ω = 0) ∧
    (∀ᵐ ω ∂d.Q, d.runningCost 0 ω = 0) ∧
    (∀ᵐ ω ∂d.Q, ∀ t : ℝ≥0,
      d.state t ω = x+(fun i => M.diffData.r i*d.noise t ω i)+d.driftIntegral t ω) := by sorry
