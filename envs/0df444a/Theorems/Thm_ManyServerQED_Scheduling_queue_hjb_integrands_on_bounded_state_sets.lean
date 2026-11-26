-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_integrands_on_bounded_state_sets
-- name    : ManyServerQED.Scheduling.queue_hjb_integrands_on_bounded_state_sets
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:49:30.477033+00:00
-- url     : https://prove2.me/theorems/d5ebbafc-e6e1-50f4-b64b-5e68fbab9ad0
-- title:
--   Bounds and continuity for accumulated HJB observations
-- statement:
--   For a twice continuously differentiable HJB solution, the running cost and HJB gap integrands are continuous, nonnegative on the control simplex, and locally bounded jointly in time and state uniformly over controls. The drift has linear growth uniformly over controls.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
open Filter Topology Set MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

theorem ManyServerQED.Scheduling.queue_hjb_integrands_on_bounded_state_sets {k : ℕ}
    (D : DiffusionData k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (ϱ mL : ℝ) (hA2 : Assumption2 Lt ϱ mL) (f : (Fin k → ℝ) → ℝ)
    (hH : IsHJBSolution D (costOfTilde Lt) γ f) :
    let L := costOfTilde Lt
    let c (t : ℝ) (z u : Fin k → ℝ) := Real.exp (-γ*t)*L z u
    let g (t : ℝ) (z u : Fin k → ℝ) := Real.exp (-γ*t)*
      ((∑ i, drift D z u i*grad f z i)+L z u-hamiltonian D L z (grad f z))
    Continuous (Function.uncurry L) ∧
    Continuous (Function.uncurry (fun t => Function.uncurry (c t))) ∧
    Continuous (Function.uncurry (fun t => Function.uncurry (g t))) ∧
    (∀ t z u, u ∈ stdSimplex ℝ (Fin k) → 0 ≤ c t z u ∧ 0 ≤ g t z u) ∧
    (∃ a > 0, ∀ z u, u ∈ stdSimplex ℝ (Fin k) →
      ∀ i, |drift D z u i| ≤ a*(1+l1norm z)) ∧
    ∀ T B : ℝ, ∃ A > 0, ∀ t ∈ Icc (0:ℝ) T, ∀ z u,
      ‖z‖ ≤ B → u ∈ stdSimplex ℝ (Fin k) →
      (∀ i, |drift D z u i| ≤ A) ∧ |c t z u| ≤ A ∧ |g t z u| ≤ A := by sorry
