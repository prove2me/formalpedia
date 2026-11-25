-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_diffusion_drift_remainder_uoc
-- name    : ManyServerQED.Scheduling.queue_diffusion_drift_remainder_uoc
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T20:37:03.807176+00:00
-- url     : https://prove2.me/theorems/e26afbcb-b3f2-42d8-ace4-c6563f9d9aac
-- title:
--   Negligible drift coefficient error in the scaled queue equation
-- statement:
--   For any work-conserving controlled many-server queue sequence with converging scaled initial conditions, subtract the initial state, centered arrival noise, time-changed centered service and abandonment noise, and the integral of the limiting diffusion drift from the scaled state. The resulting remainder tends to zero uniformly on compact time intervals in probability.

import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_Policy
open MeasureTheory Set Filter Topology ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_diffusion_drift_remainder_uoc {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n))
    (u0 : Fin k → ℝ) :
    UocInProb M.P (fun n ω t i => M.Xhat n (X n) ω t i - M.Xhat0 n (X0 n) i -
        (M.Ahat n ω t i - M.Rhat n ω (queueTime (X n) (Ψ n) ω i t / (n:ℝ)) i -
        M.Shat n ω (busyTime (Ψ n) ω i t / (n:ℝ)) i) -
        ∫ s in (0:ℝ)..t, drift M.diffData (M.Xhat n (X n) ω s)
          (uProc n u0 (X n) (Ψ n) ω s) i) (fun _ => 0) := by sorry
