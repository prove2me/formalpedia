-- Prove2me | Theorems.Thm_HryniewiczCriterion_homogeneousConvexModel_euler
-- name    : HryniewiczCriterion.homogeneousConvexModel_euler
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T17:01:40.61728+00:00
-- url     : https://prove2.me/theorems/746dccbb-91ab-4290-877f-4e2c0fd99b24
-- title:
--   Euler identities for a homogeneous convex model
-- statement:
--   Let $K$ be a homogeneous convex model, i.e. smooth on $\mathbb{R}^4\setminus\{0\}$ and positively homogeneous of degree $2$. Then for every $y\ne0$,
--   $$dK(y)\,y=2K(y),\qquad DX_K(y)\,y=X_K(y).$$
--   The second identity holds because $X_K$ is homogeneous of degree $1$. It implies that the orbit $x(t)$ itself solves the linearized equation, so the linearized flow maps $x(0)$ to $x(t)$.
-- source:
--   Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, (3.32)–(3.34), p. 220 (Euler's identity for homogeneous functions).

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.homogeneousConvexModel_euler (K : R4 → ℝ) (hK : IsHomogeneousConvexModel K) (y : R4) (hy : y ≠ 0) :
    fderiv ℝ K y y = 2 * K y ∧
      fderiv ℝ (hamiltonianVectorField K) y y = hamiltonianVectorField K y := by sorry
