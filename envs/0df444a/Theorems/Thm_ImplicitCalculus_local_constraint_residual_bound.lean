-- Prove2me | Theorems.Thm_ImplicitCalculus_local_constraint_residual_bound
-- name    : ImplicitCalculus.local_constraint_residual_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T20:19:35.963099+00:00
-- url     : https://prove2.me/theorems/aa45f5a6-397e-4aa1-a71e-814648499e43
-- title:
--   Local bound for a residual vanishing on a regular level
-- statement:
--   Let F be strictly differentiable at y with surjective derivative and finite-dimensional constraint codomain. Let H(t,z) be strictly differentiable at (t₀,y), and suppose H(s,z)=0 whenever s belongs to a prescribed time set T and F(z)=F(y). Then there is C≥0 such that ‖H(s,z)‖≤C‖F(z)−F(y)‖ for all nearby (s,z) with s∈T. No openness or closedness of T is required.
-- source:
--   Implicit function theorem and local Lipschitz estimates. Independent Banach-space generalization for the level-preservation step of Geiges, Contact geometry, https://arxiv.org/abs/math/0307242, Theorem 2.20, printed pp. 14–15. Mathlib.Analysis.Calculus.Implicit and HasStrictFDerivAt.exists_lipschitzOnWith, commit 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_ImplicitCalculus_local_level_retraction_bound
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.FDeriv.Basic

open Set Filter
open scoped Topology NNReal
set_option autoImplicit false

theorem ImplicitCalculus.local_constraint_residual_bound
    {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (F : V → W) (D : V →L[ℝ] W) (y : V)
    (hF : HasStrictFDerivAt F D y) (hD : Function.Surjective D)
    (H : ℝ × V → U) (A : (ℝ × V) →L[ℝ] U) (t : ℝ) (T : Set ℝ)
    (hH : HasStrictFDerivAt H A (t,y))
    (hzero : ∀ s ∈ T, ∀ z, F z = F y → H (s,z) = 0) :
    ∃ C : ℝ≥0, ∀ᶠ p : ℝ × V in 𝓝 (t,y),
      p.1 ∈ T → ‖H p‖ ≤ C * ‖F p.2 - F y‖ := by sorry
