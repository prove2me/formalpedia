-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_subsequential_balance
-- name    : ManyServerQED.Scheduling.queue_hjb_subsequential_balance
-- status  : Open
-- author  : @Jie Luo
-- created : 2026-11-25T20:38:24.954874+00:00
-- url     : https://prove2.me/theorems/9eb759a4-44b3-43ad-b10d-e5176947a94e
-- title:
--   Subsequential discounted HJB balance for work-conserving queue limits
-- statement:
--   For an admissible work-conserving policy sequence and a classical polynomial-growth solution $f$ of the discounted HJB equation, every subsequence of systems tending to infinity has a further subsequence along which the discounted cost converges to $\max(f(x)+g,0)$, where $g\geq0$ is the limiting accumulated Hamiltonian gap in the discounted balance. If the integrated discounted gap vanishes on compact intervals in probability, this further subsequential limit has $g=0$.
-- source:
--   Direct HJB comparison for Atar, Mandelbaum and Reiman, Theorem 4 and the P-SCP optimality conclusion, https://arxiv.org/abs/math/0407058

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_hjb_subsequential_balance {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k] (M : SystemSequence Ω k)
    (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU) (hγ : 0 < γ)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hpol : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
      IsWorkConserving n (X n) (Ψ n))
    (f : (Fin k → ℝ) → ℝ) (hf : IsC2Pol f)
    (hHJB : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    :
    ∀ s : ℕ → ℕ, Tendsto s atTop atTop →
      ∃ r : ℕ → ℕ, Tendsto r atTop atTop ∧ ∃ g : ℝ, 0 ≤ g ∧
        Tendsto (fun j => M.queueCostL (costOfTilde Lt) γ (s (r j)) u0 (X (s (r j))) (Ψ (s (r j))))
          atTop (𝓝 (ENNReal.ofReal (f x + g))) ∧
        (UocInProb M.P
      (fun n ω t => ![∫ s in (0 : ℝ)..t, Real.exp (-γ * s) *
        (∑ i, drift M.diffData (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) i *
            grad f (M.Xhat n (X n) ω s) i +
          costOfTilde Lt (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) -
          hamiltonian M.diffData (costOfTilde Lt) (M.Xhat n (X n) ω s)
            (grad f (M.Xhat n (X n) ω s)))])
      (fun _ => 0) → g = 0) := by sorry
