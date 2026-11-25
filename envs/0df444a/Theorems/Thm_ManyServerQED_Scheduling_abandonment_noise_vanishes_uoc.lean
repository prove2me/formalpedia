-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_abandonment_noise_vanishes_uoc
-- name    : ManyServerQED.Scheduling.abandonment_noise_vanishes_uoc
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T19:25:16.750718+00:00
-- url     : https://prove2.me/theorems/274874eb-0738-5ae4-868a-06ba9afea59a
-- title:
--   Time-changed abandonment noise vanishes on compact intervals
-- statement:
--   Consider work-conserving controls for the many-server systems, with convergent diffusion-scaled initial states. Let $\widehat R_i^n$ be the centered, diffusion-scaled abandonment counting process, and let $\mathring T_i^n(t)$ be the accumulated queue time for class $i$. Then the vector-valued process
--   $$t\longmapsto \big(\widehat R_i^n(\mathring T_i^n(t)/n)\big)_{i=1}^k$$
--   converges to zero uniformly on each compact calendar-time interval in probability. In the diffusion-scaled queue equation, abandonment contributes a drift but its centered noise vanishes.
-- source:
--   Atar, Mandelbaum and Reiman, Scheduling a multi class queue with many exponential servers: asymptotic optimality in heavy traffic, https://arxiv.org/pdf/math/0407058, Section 5.1 and the abandonment term of the time-changed noise in (15)–(16)

import Definitions.Def_ManyServerQED_Scheduling_Policy
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.abandonment_noise_vanishes_uoc {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n)) :
    UocInProb M.P
      (fun n ω t i => M.Rhat n ω (queueTime (X n) (Ψ n) ω i t / (n : ℝ)) i)
      (fun _ => 0) := by sorry
