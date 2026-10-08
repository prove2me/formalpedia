-- Prove2me | Theorems.Thm_HryniewiczCriterion_strictly_convex_isDynamicallyConvex
-- name    : HryniewiczCriterion.strictly_convex_isDynamicallyConvex
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T19:17:54.830208+00:00
-- url     : https://prove2.me/theorems/6899fbd8-0e49-4bbb-8a53-d794e644c539
-- title:
--   Hofer–Wysocki–Zehnder: strictly convex energy surfaces are dynamically convex
-- statement:
--   Let $H:\mathbb{R}^4\to\mathbb{R}$ be smooth and assume that $S=H^{-1}(1)$ is strictly star-shaped with respect to the origin. Assume also that $S$ is strictly convex: the Hessian of $H$ is positive definite on $T_xS$ for every $x\in S$. Then the flow of $X_H$ on $S$ is dynamically convex:
--   $$\mu_{CZ}(P)\ge3\quad\text{for every periodic orbit }P\subset S.$$
--
--   This is the theorem of Hofer, Wysocki and Zehnder that Hryniewicz quotes on p. 2. It makes every strictly convex energy level in $\mathbb{R}^4$ an instance of Theorems 1.7 and 1.8, and it shows that dynamical convexity is not vacuous.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, https://arxiv.org/abs/1105.2077, p. 2 (citing Hofer-Wysocki-Zehnder, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994)

import Definitions.Def_HryniewiczCriterion_ConleyZehnder

namespace HryniewiczCriterion

/-- Hofer–Wysocki–Zehnder (cited in Hryniewicz, p. 2): the flow on a strictly convex,
strictly star-shaped energy surface in `ℝ⁴` is dynamically convex. -/
theorem strictly_convex_isDynamicallyConvex (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (hC : IsStrictlyConvexLevel H) :
    IsDynamicallyConvex H := by sorry

end HryniewiczCriterion
