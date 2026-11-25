-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_discounted_cost_tails
-- name    : ManyServerQED.Scheduling.queue_discounted_cost_tails
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T20:48:47.953984+00:00
-- url     : https://prove2.me/theorems/e188495f-b698-58cf-8abd-f12d15186cd2
-- title:
--   Uniform discounted cost tails for measurable work-conserving queue sequences
-- statement:
--   Under the heavy-traffic and cost moment hypotheses, suppose the state and allocation processes of the admissible work-conserving policies are jointly measurable in time and the sample point. The expected discounted cost accumulated after time $T$ tends to zero uniformly over all sufficiently large system sizes.
-- source:
--   Direct HJB comparison for Atar, Mandelbaum and Reiman, Theorem 4 and the P-SCP optimality conclusion, https://arxiv.org/abs/math/0407058

import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_Policy
open MeasureTheory Set Filter Topology ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy
open scoped ENNReal NNReal

theorem ManyServerQED.Scheduling.queue_discounted_cost_tails {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU) (hγ : 0 < γ)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hPol : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
      IsWorkConserving n (X n) (Ψ n))
    (hX : ∀ n, 1 ≤ n → Measurable (fun z : Ω × ℝ≥0 => X n z.1 z.2))
    (hΨ : ∀ n, 1 ≤ n → Measurable (fun z : Ω × ℝ≥0 => Ψ n z.1 z.2)) :
    ∃ N : ℕ, ∀ ε : ℝ≥0∞, 0 < ε → ∃ T : ℕ, ∀ n ≥ N,
      (∫⁻ ω, ∫⁻ t in Ioi (T:ℝ),
        ENNReal.ofReal (Real.exp (-γ*t) * costOfTilde Lt (M.Xhat n (X n) ω t)
          (uProc n u0 (X n) (Ψ n) ω t)) ∂volume ∂M.P) < ε := by sorry
