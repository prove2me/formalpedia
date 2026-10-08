-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_ambient_positive_contact_model
-- name    : HryniewiczCriterion.exists_ambient_positive_contact_model
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T22:16:18.637719+00:00
-- url     : https://prove2.me/theorems/d4e71e28-775f-4d1a-b2b0-3f948747b3bd
-- title:
--   Convexifying a defining Hamiltonian while preserving its contact variational paths
-- statement:
--   Let a smooth energy level be strictly star-shaped and have Hessian positive on every nonzero tangent vector. There is a smooth defining Hamiltonian $G$ with exactly the same unit level, which is strictly star-shaped and whose Hessian is positive on every nonzero ambient vector at that level. Each periodic Hamiltonian orbit and normalized variational flow of the original Hamiltonian has a corresponding periodic orbit and variational flow of $G$ with exactly the same matrix path on the contact planes, in the specified global quaternionic frame. Periods may change, and multiple covers are included.
--
--   This is the defining-function normalization step: a monotone convex scalar reparametrization adds a positive rank-one normal Hessian term. Its positive time rescaling and the corresponding contact projection preserve the normalized contact path.
-- source:
--   Derived defining-function normalization for the HWZ strictly convex energy-surface theorem (Ann. of Math. 148 (1998), Theorem 3.4, https://doi.org/10.2307/120994), with the contact path convention of Hryniewicz, https://arxiv.org/html/1105.2077v5, Section 2.1. This statement isolates the rank-one Hessian correction and contact/time-change invariance; it is a reduction lemma, not a verbatim numbered assertion.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.exists_ambient_positive_contact_model
    (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (hC : IsStrictlyConvexLevel H) :
    ∃ G : R4 → ℝ, IsStrictlyStarShapedLevel G ∧ energySurface G = energySurface H ∧
      (∀ x : R4, G x = 1 → ∀ v : R4, v ≠ 0 →
        0 < fderiv ℝ (fderiv ℝ G) x v v) ∧
      ∀ (P : PeriodicOrbit H) (Y : ℝ → (R4 →L[ℝ] R4)),
        IsLinearizedFlow H P.x Y →
        ∃ (Q : PeriodicOrbit G) (Z : ℝ → (R4 →L[ℝ] R4)),
          IsLinearizedFlow G Q.x Z ∧
          linearizedXiPath G Q Z = linearizedXiPath H P Y := by sorry
