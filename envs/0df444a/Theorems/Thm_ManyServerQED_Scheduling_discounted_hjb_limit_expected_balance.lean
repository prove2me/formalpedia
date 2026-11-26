-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_discounted_hjb_limit_expected_balance
-- name    : ManyServerQED.Scheduling.discounted_hjb_limit_expected_balance
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:23:32.146586+00:00
-- url     : https://prove2.me/theorems/3a25dfcd-3376-5a4f-9c13-6c75c1c21479
-- title:
--   Expected discounted HJB identity for a subsequential limit
-- statement:
--   For a Brownian-driven limit state with at most linearly growing drift, assume the nonnegative accumulated cost and gap satisfy the pathwise drift and Hamiltonian identity, and the state supremum has integrable powers on finite time intervals. A classical polynomial-growth HJB solution then gives the finite-horizon expected cost as its initial value minus its expected discounted terminal value plus the expected gap. The gap is integrable.
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

theorem ManyServerQED.Scheduling.discounted_hjb_limit_expected_balance {k : ℕ} [NeZero k] (D : DiffusionData k)
    (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL γ : ℝ)
    (hL : CostAssumptions L ϱ mL) (hγ : 0 < γ)
    (x : Fin k → ℝ) (f : (Fin k → ℝ) → ℝ)
    (hf : IsC2Pol f) (hHJB : IsHJBSolution D L γ f)
    (d : HJBCostLimit D L γ f x)
    (hb : ∃ a : ℝ, 0 ≤ a ∧ ∀ ω t, ‖d.b t ω‖ ≤ a*(1+l1norm (d.X t ω)))
    (hsup : ∀ (T : ℝ≥0) (q : ℕ), ∃ V : d.Ω → ℝ, Integrable V d.P ∧
      ∀ᵐ ω ∂d.P, ∀ t ≤ T, l1norm (d.X t ω)^q ≤ V ω) :
    ∀ T : ℝ≥0,
      Integrable (d.gap T) d.P ∧
      (∫ ω, d.cost T ω ∂d.P) =
        f x - (∫ ω, Real.exp (-γ * (T:ℝ)) * f (d.X T ω) ∂d.P) +
          ∫ ω, d.gap T ω ∂d.P := by sorry
