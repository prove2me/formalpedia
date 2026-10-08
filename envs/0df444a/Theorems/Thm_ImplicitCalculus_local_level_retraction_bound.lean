-- Prove2me | Theorems.Thm_ImplicitCalculus_local_level_retraction_bound
-- name    : ImplicitCalculus.local_level_retraction_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T20:16:25.870508+00:00
-- url     : https://prove2.me/theorems/e1aed8a1-e7f1-42f0-8190-30059ce3883e
-- title:
--   Local retraction onto a regular level with a constraint-error bound
-- statement:
--   A strictly differentiable map from a real Banach space to a finite-dimensional real normed space, with surjective derivative at y, admits a continuous local retraction r onto the level through y. It fixes y, and for some nonnegative constant C, every sufficiently nearby z satisfies F(r(z))=F(y) and dist(z,r(z))≤C‖F(z)−F(y)‖.
-- source:
--   Implicit function theorem and local Lipschitz estimates. Independent Banach-space generalization for the level-preservation step of Geiges, Contact geometry, https://arxiv.org/abs/math/0307242, Theorem 2.20, printed pp. 14–15. Mathlib.Analysis.Calculus.Implicit and HasStrictFDerivAt.exists_lipschitzOnWith, commit 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.FDeriv.Basic

open Set Filter
open scoped Topology NNReal
set_option autoImplicit false

theorem ImplicitCalculus.local_level_retraction_bound
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (F : V → W) (D : V →L[ℝ] W) (y : V)
    (hF : HasStrictFDerivAt F D y) (hD : Function.Surjective D) :
    ∃ r : V → V, ContinuousAt r y ∧ r y = y ∧
      ∃ C : ℝ≥0, ∀ᶠ z in 𝓝 y,
        F (r z) = F y ∧ dist z (r z) ≤ C * ‖F z - F y‖ := by sorry
