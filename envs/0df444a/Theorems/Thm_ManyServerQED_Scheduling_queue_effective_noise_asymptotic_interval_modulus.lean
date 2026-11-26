-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_effective_noise_asymptotic_interval_modulus
-- name    : ManyServerQED.Scheduling.queue_effective_noise_asymptotic_interval_modulus
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:32:00.830884+00:00
-- url     : https://prove2.me/theorems/72724e1c-3639-409c-8266-d33dff60c81d
-- title:
--   Asymptotic interval modulus of normalized queue noise
-- statement:
--   The standardized effective noise of a work-conserving controlled queue row has a vanishing interval oscillation modulus in probability on each compact horizon.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_queue_effective_noise_reference_and_future_approximations
import Theorems.Thm_ManyServerQED_Scheduling_queue_arrival_norm_and_modulus_bounds
import Theorems.Thm_ManyServerQED_Scheduling_poisson_rows_centered_interval_modulus_bound
import Theorems.Thm_ManyServerQED_Scheduling_poisson_primitive_deterministic_clock_change
import Theorems.Thm_ManyServerQED_Scheduling_finite_family_independent_continuous_brownian
open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_effective_noise_asymptotic_interval_modulus {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (mL mU : ℝ) (hA3 : M.Assumption3 mL mU)
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n))
    (i : Fin k) (T : ℕ) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    let w (n : ℕ) (ω : Ω) (t : ℝ) :=
      (M.Ahat n ω t i-M.Shat n ω (busyTime (Ψ n) ω i t/(n:ℝ)) i-
        M.Rhat n ω (queueTime (X n) (Ψ n) ω i t/(n:ℝ)) i)/M.diffData.r i
    ∃ δ > 0, ∀ᶠ n in atTop,
      M.P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ |w n ω s-w n ω t|} ≤ ENNReal.ofReal η := by sorry
