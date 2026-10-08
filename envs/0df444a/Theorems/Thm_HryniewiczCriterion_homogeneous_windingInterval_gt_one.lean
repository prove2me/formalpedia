-- Prove2me | Theorems.Thm_HryniewiczCriterion_homogeneous_windingInterval_gt_one
-- name    : HryniewiczCriterion.homogeneous_windingInterval_gt_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T15:22:46.722077+00:00
-- url     : https://prove2.me/theorems/ef6ea08d-714f-4bf9-89b1-2f84f424a4a3
-- title:
--   HWZ winding bound for a homogeneous convex model
-- statement:
--   Let $K$ be a homogeneous convex model: smooth on $\mathbb{R}^4\setminus\{0\}$, positively homogeneous of degree two, positive away from $0$, with Hessian positive definite on all vectors at every point of $S=K^{-1}(1)$. Let $Q=(x,T)$ be a periodic orbit of $X_K$ on $S$, prime or multiply covered, with normalized variational flow $Z$, and let $\varphi$ be its contact-plane path in the global frame $Z_1,Z_2$. Then the winding interval of $\varphi$ lies in $(1,\infty)$:
--   $$\Delta>1\qquad\text{for every }\Delta\in I(\varphi).$$
--   Equivalently, every nonzero vector of $\xi_{x(0)}$ turns strictly more than once relative to the frame under the linearized flow over one period. This is the core estimate in the proof of HWZ Theorem 3.4.
-- source:
--   Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, Theorem 3.4 and its proof, pp. 219–222, (3.32)–(3.46), stated in the winding form of Hryniewicz, https://arxiv.org/html/1105.2077v5, Section 2.1.1, equations (4)–(5).

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.homogeneous_windingInterval_gt_one (K : R4 → ℝ) (hK : IsHomogeneousConvexModel K)
    (Q : PeriodicOrbit K) (Z : ℝ → (R4 →L[ℝ] R4)) (hZ : IsLinearizedFlow K Q.x Z) :
    ∀ d ∈ windingInterval (linearizedXiPath K Q Z), 1 < d := by sorry
