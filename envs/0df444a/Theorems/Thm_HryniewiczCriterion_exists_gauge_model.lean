-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_gauge_model
-- name    : HryniewiczCriterion.exists_gauge_model
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T19:53:39.379557+00:00
-- url     : https://prove2.me/theorems/a26ccf5f-bbc3-42b2-9167-a1cc036c328d
-- title:
--   The squared Minkowski gauge of a star-shaped level is a homogeneous convex model
-- statement:
--   Let $H:\mathbb{R}^4\to\mathbb{R}$ be smooth with strictly star-shaped unit level $S=H^{-1}(1)$, and let the Hessian of $H$ be positive definite on all of $\mathbb{R}^4$ at every point of $S$. Let $K=\rho^2$, where $\rho$ is the Minkowski gauge of the domain bounded by $S$. Then $K$ is a homogeneous convex model with $K^{-1}(1)=S$. On $S$ its differential is $dK(y)=\dfrac{2}{dH(y)\,y}\,dH(y)$, so $X_K=\dfrac{2}{dH(y)\,y}\,X_H$ there.
--
--   Proof idea: $\rho$ is smooth off $0$ by the implicit function theorem applied to $H(s\,x)=1$. On $S$, $D^2K(x)(x,x)=2$ and $D^2K(x)(x,w)=0$ for $w\in T_xS$, while $D^2K(x)(w,w)=\frac{2}{dH(x)x}D^2H(x)(w,w)$.
-- source:
--   Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, (3.32), p. 219: K is the square of the Minkowski functional of the domain bounded by S; the formula for dK on S follows from Euler's identity dK(x)x = 2.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.exists_gauge_model (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (hpos : ∀ x : R4, H x = 1 → ∀ v : R4, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ H) x v v) :
    ∃ K : R4 → ℝ, IsHomogeneousConvexModel K ∧ energySurface K = energySurface H ∧
      ∀ y : R4, H y = 1 → fderiv ℝ K y = (2 / fderiv ℝ H y y) • fderiv ℝ H y := by sorry
