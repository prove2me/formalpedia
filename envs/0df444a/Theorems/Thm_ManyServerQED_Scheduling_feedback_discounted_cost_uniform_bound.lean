-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_feedback_discounted_cost_uniform_bound
-- name    : ManyServerQED.Scheduling.feedback_discounted_cost_uniform_bound
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T19:32:08.781773+00:00
-- url     : https://prove2.me/theorems/c5f2e567-d0e5-4051-9c34-5bd21bb2fd6b
-- title:
--   Uniform finite bound for discounted feedback queue costs
-- statement:
--   For the many-server systems, let the diffusion-scaled initial state converge. Take any sequence of work-conserving admissible state-feedback policies and suppose the running cost and interarrival distribution satisfy Assumptions 2 and 3. For every strictly positive discount rate, the expected discounted costs are bounded above by a finite common constant for all sufficiently large system sizes. In particular, the limiting lower bound provided by the diffusion value is finite once the cost lower bound theorem is applied to this sequence.
-- source:
--   Atar, Mandelbaum and Reiman, https://arxiv.org/pdf/math/0407058, Assumptions 2 and 3, Lemma 3 (p. 32), and the discounted cost bounds in the proof of Theorem 4

import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory Filter Topology
open scoped ENNReal
open ManyServerQED.Scheduling

theorem ManyServerQED.Scheduling.feedback_discounted_cost_uniform_bound {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU) (hγ : 0 < γ)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (Y : ℕ → Ω → ℝ → Fin k → ℕ) (F : ℕ → (Fin k → ℕ) → Fin k → ℕ)
    (hF : ∀ n v i, F n v i ≤ v i)
    (hPol : ∀ n, 1 ≤ n →
      let X : Ω → ℝ → Fin k → ℝ := fun ω t i => (Y n ω t i : ℝ)
      let Ψ : Ω → ℝ → Fin k → ℝ := fun ω t i => (F n (Y n ω t) i : ℝ)
      M.IsSCP n (X0 n) X Ψ ∧ M.IsAdmissible n X Ψ ∧ IsWorkConserving n X Ψ) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ᶠ n in atTop,
      M.queueCostL (costOfTilde Lt) γ n u0 (fun ω t i => (Y n ω t i : ℝ))
        (fun ω t i => (F n (Y n ω t) i : ℝ)) ≤ K := by sorry
