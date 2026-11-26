-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_state_sup_polynomial_moment
-- name    : ManyServerQED.Scheduling.queue_state_sup_polynomial_moment
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:06:12.649373+00:00
-- url     : https://prove2.me/theorems/96f38a68-51e0-420c-acc3-ce800c6b6adf
-- title:
--   Polynomial maximal moments of the diffusion-scaled queue state
-- statement:
--   Consider a sequence of admissible work-conserving queueing policies under the moment assumptions of the many-server model, starting at states converging on the diffusion scale. The moment of order $m_U$ of the path supremum of the diffusion-scaled state up to time $t$ is bounded by a constant times a polynomial in $t$ and in the norm of the limiting initial state, uniformly for all sufficiently large system sizes.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_Policy
import Theorems.Thm_ManyServerQED_Scheduling_work_conserving_pathwise_growth
import Theorems.Thm_ManyServerQED_Scheduling_queue_forcing_polynomial_moment
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_state_sup_polynomial_moment {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (mL mU : ℝ)
    (hA3 : M.Assumption3 mL mU) :
    ∃ (c : ℝ) (mbar : ℕ), ∀ (x : Fin k → ℝ) (X0 : ℕ → Fin k → ℕ),
      Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x) →
      ∀ (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ),
      (∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
        IsWorkConserving n (X n) (Ψ n)) →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, (supDist (M.Xhat n (X n) ω) (fun _ => 0) t) ^ mU ∂M.P ≤
        ENNReal.ofReal (c * (1 + l1norm x ^ mbar) * (1 + t ^ mbar)) := by sorry
