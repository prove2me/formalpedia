-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_cost_comparison
-- name    : ManyServerQED.Scheduling.queue_hjb_cost_comparison
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T20:24:14.403287+00:00
-- url     : https://prove2.me/theorems/a76c1953-be30-57fa-aba3-7940f220e3ed
-- title:
--   Direct HJB lower bound and zero-gap upper bound for the discounted queue cost
-- statement:
--   Under the many-server heavy-traffic hypotheses, let $f$ be a polynomial-growth classical solution of the discounted HJB equation. For every sequence of admissible work-conserving policies, the limit inferior of its discounted diffusion-scaled costs is at least $f(x)$ whenever $f(x)geq0$, with the bound expressed on extended nonnegative reals. If the integrated discounted Hamiltonian gap converges to zero uniformly on compact time intervals in probability, the limit superior is at most $max{f(x),0}$. The comparison uses the given HJB solution directly.
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

theorem ManyServerQED.Scheduling.queue_hjb_cost_comparison {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k] (M : SystemSequence Ω k)
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
    ENNReal.ofReal (f x) ≤ liminf (fun n => M.queueCostL (costOfTilde Lt) γ n u0 (X n) (Ψ n)) atTop ∧
      ((UocInProb M.P
      (fun n ω t => ![∫ s in (0 : ℝ)..t, Real.exp (-γ * s) *
        (∑ i, drift M.diffData (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) i *
            grad f (M.Xhat n (X n) ω s) i +
          costOfTilde Lt (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) -
          hamiltonian M.diffData (costOfTilde Lt) (M.Xhat n (X n) ω s)
            (grad f (M.Xhat n (X n) ω s)))])
      (fun _ => 0)) →
        limsup (fun n => M.queueCostL (costOfTilde Lt) γ n u0 (X n) (Ψ n)) atTop ≤ ENNReal.ofReal (f x)) := by sorry
