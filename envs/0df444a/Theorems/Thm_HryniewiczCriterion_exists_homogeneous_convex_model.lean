-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_homogeneous_convex_model
-- name    : HryniewiczCriterion.exists_homogeneous_convex_model
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T15:22:45.836251+00:00
-- url     : https://prove2.me/theorems/11146522-354a-4a14-9d04-eb913a6ef9a6
-- title:
--   Homogeneous convex model of a level with positive ambient Hessian
-- statement:
--   Let $H:\mathbb{R}^4\to\mathbb{R}$ be smooth with strictly star-shaped unit level $S=H^{-1}(1)$, and assume the Hessian of $H$ is positive definite on all of $\mathbb{R}^4$ at every point of $S$. Then there is a function $K$ with the same unit level which is a *homogeneous convex model*: $K$ is smooth on $\mathbb{R}^4\setminus\{0\}$, positively homogeneous of degree two ($K(rx)=r^2K(x)$ for $r>0$), positive away from the origin, and its Hessian is positive definite on all vectors at every point of $S$.
--
--   Moreover, for every periodic orbit $P$ of $X_H$ on $S$ (prime or multiply covered) with normalized variational flow $Y$, there are a periodic orbit $Q$ of $X_K$ and a normalized variational flow $Z$ along it such that the contact-plane paths of $(H,P,Y)$ and $(K,Q,Z)$ in the global frame $Z_1,Z_2$ have the same winding interval.
--
--   This is the normalization step of HWZ (3.31)–(3.32), where $K$ is the square of the Minkowski functional of the domain bounded by $S$. It lets the index estimate be proved for degree-two homogeneous Hamiltonians only, for which the linearized flow has an invariant splitting.
-- source:
--   Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, Section 3, (3.31)–(3.32) and Lemma 3.5, pp. 219–220; contact path convention of Hryniewicz, https://arxiv.org/html/1105.2077v5, Section 2.1.1, equations (4)–(5). Reduction lemma isolating the choice of the homogeneous defining function; not a verbatim numbered assertion.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.exists_homogeneous_convex_model (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (hpos : ∀ x : R4, H x = 1 → ∀ v : R4, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ H) x v v) :
    ∃ K : R4 → ℝ, IsHomogeneousConvexModel K ∧ energySurface K = energySurface H ∧
      ∀ (P : PeriodicOrbit H) (Y : ℝ → (R4 →L[ℝ] R4)), IsLinearizedFlow H P.x Y →
        ∃ (Q : PeriodicOrbit K) (Z : ℝ → (R4 →L[ℝ] R4)), IsLinearizedFlow K Q.x Z ∧
          windingInterval (linearizedXiPath K Q Z) = windingInterval (linearizedXiPath H P Y) := by sorry
