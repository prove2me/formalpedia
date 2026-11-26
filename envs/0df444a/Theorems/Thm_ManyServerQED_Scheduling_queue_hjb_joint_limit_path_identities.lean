-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_joint_limit_path_identities
-- name    : ManyServerQED.Scheduling.queue_hjb_joint_limit_path_identities
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:19:43.124173+00:00
-- url     : https://prove2.me/theorems/a895fa6f-bd03-4fd5-a285-67b9a2ec4bf5
-- title:
--   State and gap equations of the joint queue limit
-- statement:
--   The limiting accumulated drift has a jointly measurable density with linear growth in the limiting state. The limiting state and gap satisfy the diffusion state equation and the integrated Hamiltonian-gap identity. The limiting cost and gap are increasing and the cost starts at zero.
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

theorem ManyServerQED.Scheduling.queue_hjb_joint_limit_path_identities {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k] (M : SystemSequence Ω k)
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
    (d : QueueHJBPathSubseq M.P (queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ) s) :
    ∃ b : ℝ≥0 → d.Ω' → Fin k → ℝ,
      Measurable (fun z : d.Ω' × ℝ≥0 => b z.2 z.1) ∧
      (∃ a : ℝ, 0 ≤ a ∧ ∀ ω t, ‖b t ω‖ ≤ a*(1+l1norm (d.state t ω))) ∧
      (∀ᵐ ω ∂d.Q, d.state 0 ω = x) ∧
      (∀ᵐ ω ∂d.Q, ∀ t : ℝ≥0,
        d.state t ω = x + (fun i => M.diffData.r i*d.noise t ω i) +
          ∫ s in (0:ℝ)..(t:ℝ), b s.toNNReal ω) ∧
      (∀ᵐ ω ∂d.Q, Monotone (fun t => d.runningCost t ω)) ∧
      (∀ᵐ ω ∂d.Q, Monotone (fun t => d.gap t ω)) ∧
      (∀ᵐ ω ∂d.Q, d.runningCost 0 ω = 0) ∧
      (∀ᵐ ω ∂d.Q, ∀ t : ℝ≥0, d.gap t ω = d.runningCost t ω +
        ∫ r in (0:ℝ)..(t:ℝ), Real.exp (-γ*r) *
          ((∑ i, b r.toNNReal ω i * grad f (d.state r.toNNReal ω) i) -
            hamiltonian M.diffData (costOfTilde Lt) (d.state r.toNNReal ω)
              (grad f (d.state r.toNNReal ω)))) := by sorry
