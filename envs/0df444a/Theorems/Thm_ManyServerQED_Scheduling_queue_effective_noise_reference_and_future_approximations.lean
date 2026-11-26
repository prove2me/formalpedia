-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_effective_noise_reference_and_future_approximations
-- name    : ManyServerQED.Scheduling.queue_effective_noise_reference_and_future_approximations
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:25:11.332864+00:00
-- url     : https://prove2.me/theorems/2b7cb801-6c21-5e4e-a56a-40182ec775f1
-- title:
--   Uniform approximations of the effective queue noise
-- statement:
--   On a fixed compact interval, the normalized effective noise is uniformly close in probability to the arrival noise minus the service noise at the fluid clock. On an interval after a fixed time its increments are also uniformly close to the normalized difference of the independently observed restarted primitive suffixes.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_centered_queue_service_noise_clock_approximations
import Theorems.Thm_ManyServerQED_Scheduling_centered_queue_arrival_noise_restarted_clock_approximation
import Theorems.Thm_ManyServerQED_Scheduling_abandonment_noise_vanishes_uoc
import Mathlib
open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal
open Finset
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_effective_noise_reference_and_future_approximations {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (mL mU : ℝ) (hA3 : M.Assumption3 mL mU)
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n))
    (i : Fin k) (b : ℝ) (hb : 0 ≤ b) (T : ℝ) (hT : b ≤ T) :
    let A (n : ℕ) (ω : Ω) (t : ℝ) := M.Ahat n ω t i
    let S (n : ℕ) (ω : Ω) (t : ℝ) := M.Shat n ω t i
    let R (n : ℕ) (ω : Ω) (t : ℝ) :=
      M.Rhat n ω (queueTime (X n) (Ψ n) ω i t/(n:ℝ)) i
    let c (n : ℕ) (ω : Ω) (t : ℝ) := busyTime (Ψ n) ω i t/(n:ℝ)
    let w (n : ℕ) (ω : Ω) (t : ℝ) := (A n ω t-S n ω (c n ω t)-R n ω t)/M.diffData.r i
    let z (n : ℕ) (ω : Ω) (t : ℝ) := (A n ω t-S n ω (M.rho i*t))/M.diffData.r i
    let a (n : ℕ) (ω : Ω) := M.nextArrival n i ω b
    let V (n : ℕ) (ω : Ω) (t : ℝ) :=
      (A n ω (a n ω+(t-b))-A n ω (a n ω) -
        (S n ω (c n ω b+M.rho i*(t-b))-S n ω (c n ω b)))/M.diffData.r i
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T, ε ≤ |w n ω t-z n ω t|}) atTop (𝓝 0) ∧
      Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T, ε ≤ |V n ω t-(w n ω t-w n ω b)|})
        atTop (𝓝 0) := by sorry
