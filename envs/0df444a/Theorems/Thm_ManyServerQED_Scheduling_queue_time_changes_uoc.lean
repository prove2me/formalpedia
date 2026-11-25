-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_time_changes_uoc
-- name    : ManyServerQED.Scheduling.queue_time_changes_uoc
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T19:21:49.39202+00:00
-- url     : https://prove2.me/theorems/7c2f8589-94e4-5fde-978d-b7262d087c19
-- title:
--   Fluid service and abandonment clocks converge uniformly on compact intervals in probability
-- statement:
--   In the many-server system, assume that the diffusion-scaled initial states converge and that every system uses a work-conserving control. For class $i$, let $T_i^n(t)$ and $\mathring T_i^n(t)$ be the service and abandonment operational clocks. Then the vector of divided service clocks converges to the deterministic linear clock and the vector of divided abandonment clocks converges to zero:
--   $$n^{-1}T_i^n(t)\longrightarrow \rho_i t,\qquad n^{-1}\mathring T_i^n(t)\longrightarrow 0.$$
--   Both convergences are uniform on every bounded calendar-time interval in probability. This identifies the time changes that occur in the diffusion limit.
-- source:
--   Atar, Mandelbaum and Reiman, Scheduling a multi class queue with many exponential servers: asymptotic optimality in heavy traffic, https://arxiv.org/pdf/math/0407058, Section 5.1, proof of Lemma 4(i) and the primitive time changes

import Definitions.Def_ManyServerQED_Scheduling_Policy
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_time_changes_uoc {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n)) :
    UocInProb M.P (fun n ω t i => busyTime (Ψ n) ω i t / (n : ℝ))
        (fun t i => M.rho i * t) ∧
      UocInProb M.P (fun n ω t i => queueTime (X n) (Ψ n) ω i t / (n : ℝ))
        (fun _ => 0) := by sorry
