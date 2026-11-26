-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_joint_limit_moments_and_cost
-- name    : ManyServerQED.Scheduling.queue_hjb_joint_limit_moments_and_cost
-- status  : Open
-- author  : @Jie Luo
-- created : 2026-11-26T03:19:57.686547+00:00
-- url     : https://prove2.me/theorems/4baa67bd-ddef-4169-a362-8e41cbd49b00
-- title:
--   Moments and cost convergence for the joint queue limit
-- statement:
--   A continuous joint queue limit with standard Brownian driving noise has polynomial marginal state moments of all orders and an integrable supremum on each finite horizon. The limiting discounted running cost is integrable at every finite time, and finite-horizon expected costs converge along the subsequence.
-- source:
--   Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_HJBCostLimit
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_hjb_joint_limit_moments_and_cost {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k] (M : SystemSequence Ω k)
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

    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (d : QueueHJBPathSubseq M.P (queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ) s) (F : Filtration ℝ≥0 d.mΩ') (hW : IsStdFBrownian d.Q F d.noise) :
    (∀ p : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∃ j : ℕ, ∀ t : ℝ≥0,
      Integrable (fun ω => l1norm (d.state t ω)^p) d.Q ∧
      (∫ ω, l1norm (d.state t ω)^p ∂d.Q) ≤ c*(1+(t:ℝ)^j)) ∧
    (∀ (T : ℝ≥0) (q : ℕ), ∃ V : d.Ω' → ℝ, Integrable V d.Q ∧
      ∀ᵐ ω ∂d.Q, ∀ t ≤ T, l1norm (d.state t ω)^q ≤ V ω) ∧
    (∀ t, Integrable (d.runningCost t) d.Q) ∧
    (∀ T : ℕ, Tendsto (fun j =>
      ∫⁻ ω, ∫⁻ t in Set.Ioc (0:ℝ) (T:ℝ),
        ENNReal.ofReal (Real.exp (-γ*t) *
          costOfTilde Lt (M.Xhat (s (d.r j)) (X (s (d.r j))) ω t)
            (uProc (s (d.r j)) u0 (X (s (d.r j))) (Ψ (s (d.r j))) ω t))
        ∂volume ∂M.P) atTop (𝓝 (ENNReal.ofReal (∫ ω, d.runningCost T ω ∂d.Q)))) := by sorry
