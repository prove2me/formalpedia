-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_finite_horizon_cost_uniform_moment
-- name    : ManyServerQED.Scheduling.queue_finite_horizon_cost_uniform_moment
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:28:48.058833+00:00
-- url     : https://prove2.me/theorems/b5b5400a-5169-4676-97a4-b0ca5b87a9e9
-- title:
--   Uniform higher moment of the finite-horizon queueing cost
-- statement:
--   In the many-server queue, assume admissible work-conserving policies, convergent scaled initial states, and the model and cost moment assumptions. There is an exponent strictly greater than one for which the discounted accumulated cost has uniformly bounded moments at each fixed nonnegative horizon for all sufficiently large system sizes.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_queue_state_sup_polynomial_moment
open MeasureTheory ProbabilityTheory Filter Topology Set
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy
open scoped ENNReal NNReal

theorem ManyServerQED.Scheduling.queue_finite_horizon_cost_uniform_moment {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU) (hγ : 0 < γ)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hPol : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
      IsWorkConserving n (X n) (Ψ n)) :
    ∃ p : ℝ, 1 < p ∧ ∀ T : ℝ, 0 ≤ T → ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ᶠ n in atTop,
      (∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) T,
        ENNReal.ofReal (Real.exp (-γ*t) * costOfTilde Lt (M.Xhat n (X n) ω t)
          (uProc n u0 (X n) (Ψ n) ω t)) ∂volume)^p ∂M.P) ≤ K := by sorry
