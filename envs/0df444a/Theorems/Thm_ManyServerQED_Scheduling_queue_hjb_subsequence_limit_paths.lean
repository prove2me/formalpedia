-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_subsequence_limit_paths
-- name    : ManyServerQED.Scheduling.queue_hjb_subsequence_limit_paths
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:23:40.784297+00:00
-- url     : https://prove2.me/theorems/5ed276ed-0e73-4eb6-9dce-4691248fecbb
-- title:
--   Brownian queueing limit with accumulated HJB cost and gap
-- statement:
--   Consider any cofinal subsequence of admissible work-conserving systems. It has a cofinal further subsequence with a Brownian-driven limit state and continuous accumulated cost and Hamiltonian gap processes. The state satisfies the integrated limit drift equation, the cost expectations converge on each integer horizon, and the limiting Hamiltonian gap vanishes if the prelimit gaps converge to zero in probability uniformly on compact time intervals. The drift grows at most linearly and the state supremum has moments of every integral order on each finite interval.
-- source:
--   Atar, Mandelbaum and Reiman, Scheduling a multi class queue with many exponential servers, proof of Theorem 4. https://arxiv.org/abs/math/0407058

import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_HJBCostLimit
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_hjb_subsequence_limit_paths {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k] (M : SystemSequence Ω k)
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
      ∃ r : ℕ → ℕ, Tendsto r atTop atTop ∧
      ∃ d : HJBCostLimit M.diffData (costOfTilde Lt) γ f x,
        (∀ T : ℕ, Tendsto (fun j =>
          ∫⁻ ω, ∫⁻ t in Set.Ioc (0:ℝ) (T:ℝ),
            ENNReal.ofReal (Real.exp (-γ*t) *
              costOfTilde Lt (M.Xhat (s (r j)) (X (s (r j))) ω t)
                (uProc (s (r j)) u0 (X (s (r j))) (Ψ (s (r j))) ω t)) ∂volume ∂M.P)
          atTop (𝓝 (ENNReal.ofReal (∫ ω, d.cost T ω ∂d.P)))) ∧
        (∃ a : ℝ, 0 ≤ a ∧ ∀ ω t, ‖d.b t ω‖ ≤ a*(1+l1norm (d.X t ω))) ∧
        (∀ (T : ℝ≥0) (q : ℕ), ∃ V : d.Ω → ℝ, Integrable V d.P ∧
          ∀ᵐ ω ∂d.P, ∀ t ≤ T, l1norm (d.X t ω)^q ≤ V ω) ∧
        (UocInProb M.P
      (fun n ω t => ![∫ s in (0 : ℝ)..t, Real.exp (-γ * s) *
        (∑ i, drift M.diffData (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) i *
            grad f (M.Xhat n (X n) ω s) i +
          costOfTilde Lt (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) -
          hamiltonian M.diffData (costOfTilde Lt) (M.Xhat n (X n) ω s)
            (grad f (M.Xhat n (X n) ω s)))])
      (fun _ => 0) → ∀ T : ℕ, ∀ᵐ ω ∂d.P, d.gap T ω = 0) := by sorry
