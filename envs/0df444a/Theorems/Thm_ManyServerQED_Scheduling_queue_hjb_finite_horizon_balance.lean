-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_finite_horizon_balance
-- name    : ManyServerQED.Scheduling.queue_hjb_finite_horizon_balance
-- status  : Open
-- author  : @Jie Luo
-- created : 2026-11-25T20:48:56.071851+00:00
-- url     : https://prove2.me/theorems/a1792aad-3545-4ed5-b17f-3d18f3bd9a54
-- title:
--   Discounted HJB identity on finite-horizon queue limit paths
-- statement:
--   Along a further subsequence of any sequence of system sizes tending to infinity, let $C_T$ denote the limit of the expected costs up to integer horizon $T$. Then $C_T=f(x)-F_T+G_T$, where $F_T$ is the discounted terminal expectation and tends to zero as $T\to\infty$, and $G_T\geq0$ is the expected discounted accumulated Hamiltonian gap. The integrated gap condition forces $G_T=0$ at every finite horizon.
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

theorem ManyServerQED.Scheduling.queue_hjb_finite_horizon_balance {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k] (M : SystemSequence Ω k)
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
      ∃ r : ℕ → ℕ, Tendsto r atTop atTop ∧ ∃ C F G : ℕ → ℝ,
        (∀ T, 0 ≤ C T ∧ 0 ≤ G T ∧ C T = f x - F T + G T) ∧
        Tendsto F atTop (𝓝 0) ∧
        (∀ T : ℕ, Tendsto (fun j =>
          ∫⁻ ω, ∫⁻ t in Set.Ioc (0:ℝ) (T:ℝ),
            ENNReal.ofReal (Real.exp (-γ*t) *
              costOfTilde Lt (M.Xhat (s (r j)) (X (s (r j))) ω t)
                (uProc (s (r j)) u0 (X (s (r j))) (Ψ (s (r j))) ω t)) ∂volume ∂M.P)
          atTop (𝓝 (ENNReal.ofReal (C T)))) ∧
        (UocInProb M.P
      (fun n ω t => ![∫ s in (0 : ℝ)..t, Real.exp (-γ * s) *
        (∑ i, drift M.diffData (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) i *
            grad f (M.Xhat n (X n) ω s) i +
          costOfTilde Lt (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) -
          hamiltonian M.diffData (costOfTilde Lt) (M.Xhat n (X n) ω s)
            (grad f (M.Xhat n (X n) ω s)))])
      (fun _ => 0) → ∀ T, G T = 0) := by sorry
