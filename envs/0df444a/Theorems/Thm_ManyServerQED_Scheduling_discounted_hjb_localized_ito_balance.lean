-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_discounted_hjb_localized_ito_balance
-- name    : ManyServerQED.Scheduling.discounted_hjb_localized_ito_balance
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:23:35.253802+00:00
-- url     : https://prove2.me/theorems/5c5da155-8725-5c2e-850c-d0812aea0942
-- title:
--   Localized discounted Itô identity for an HJB limit
-- statement:
--   For a Brownian-driven limit state with at most linearly growing drift and continuous nonnegative accumulated cost and gap satisfying the HJB drift pairing, every finite horizon admits increasing localization times which almost surely equal the horizon for all sufficiently large localization levels. The expected stopped cost equals the initial HJB value minus the stopped terminal expectation plus the expected stopped gap.
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

theorem ManyServerQED.Scheduling.discounted_hjb_localized_ito_balance {k : ℕ} [NeZero k] (D : DiffusionData k)
    (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL γ : ℝ)
    (hL : CostAssumptions L ϱ mL) (hγ : 0 < γ)
    (x : Fin k → ℝ) (f : (Fin k → ℝ) → ℝ)
    (hf : IsC2Pol f) (hHJB : IsHJBSolution D L γ f)
    (d : HJBCostLimit D L γ f x)
    (hb : ∃ a : ℝ, 0 ≤ a ∧ ∀ ω t, ‖d.b t ω‖ ≤ a*(1+l1norm (d.X t ω))) (T : ℝ≥0) :
    ∃ τ : ℕ → d.Ω → ℝ≥0,
      (∀ R ω, τ R ω ≤ T) ∧
      (∀ ω, Monotone (fun R => τ R ω)) ∧
      (∀ᵐ ω ∂d.P, ∀ᶠ R in atTop, τ R ω = T) ∧
      (∀ R,
        Integrable (fun ω => d.cost (τ R ω) ω) d.P ∧
        Integrable (fun ω => d.gap (τ R ω) ω) d.P ∧
        Integrable (fun ω => Real.exp (-γ * (τ R ω : ℝ)) * f (d.X (τ R ω) ω)) d.P ∧
        (∫ ω, d.cost (τ R ω) ω ∂d.P) =
          f x - (∫ ω, Real.exp (-γ * (τ R ω : ℝ)) * f (d.X (τ R ω) ω) ∂d.P) +
            ∫ ω, d.gap (τ R ω) ω ∂d.P) := by sorry
