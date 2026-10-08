-- Prove2me | Theorems.Thm_HryniewiczCriterion_strictly_convex_windingInterval_gt_one
-- name    : HryniewiczCriterion.strictly_convex_windingInterval_gt_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T21:11:54.84799+00:00
-- url     : https://prove2.me/theorems/f8dbf10c-262e-4e86-9ce3-ffa334c67075
-- title:
--   Strictly convex levels: every vector of $\xi$ winds more than once
-- statement:
--   Let $H:\mathbb{R}^4\to\mathbb{R}$ be smooth, let $S=H^{-1}(1)$ be strictly star-shaped, and let $S$ be strictly convex: the Hessian of $H$ is positive definite on $T_xS=\ker dH(x)$ for every $x\in S$. Let $P=(x,T)$ be a periodic orbit of $X_H$ on $S$, prime or multiply covered, let $Y$ be its linearized flow, and let $\varphi:[0,1]\to Sp(1)$ be the linearized flow on $\xi$ in the global frame $Z_1,Z_2$. Then the winding interval lies in $(1,\infty)$:
--   $$\Delta>1\qquad\text{for every }\Delta\in I(\varphi).$$
--   In words: under the linearized Reeb flow along $P$, every nonzero vector of $\xi_{x(0)}$ turns strictly more than one full turn relative to the frame $Z_1,Z_2$.
--
--   This is the core estimate in the theorem of Hofer, Wysocki and Zehnder (1998, Theorem 3.4) that strictly convex energy surfaces are dynamically convex. Since $I(\varphi)$ is a compact interval of length less than $1/2$, the condition $I(\varphi)\subset(1,\infty)$ is equivalent to $\mu_{CZ}(P)\ge3$ for Hryniewicz's index (Section 2.1.1).
--
--   **Formalization Note** The winding interval is `windingInterval (linearizedXiPath H P Y)`. Strict convexity is `IsStrictlyConvexLevel H`: the second derivative of $H$ is positive on nonzero vectors of $\ker dH(x)$, $x\in S$.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, https://arxiv.org/abs/1105.2077, p. 2 (HWZ theorem) and Section 2.1.1, pp. 5-6 (mu >= 3 iff I(phi) lies in (1, infinity)); Hofer-Wysocki-Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998) 197-289, https://doi.org/10.2307/120994, Theorem 3.4

import Definitions.Def_HryniewiczCriterion_ConleyZehnder

namespace HryniewiczCriterion

/-- Hofer–Wysocki–Zehnder, Ann. of Math. 148 (1998), Theorem 3.4, in winding form
(Hryniewicz, arXiv:1105.2077, pp. 2 and 5–6): on a strictly convex, strictly star-shaped
level in `ℝ⁴`, every vector of `ξ` turns strictly more than once under the linearized
flow along any periodic orbit, i.e. the winding interval lies in `(1, ∞)`. -/
theorem strictly_convex_windingInterval_gt_one (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (hC : IsStrictlyConvexLevel H)
    (P : PeriodicOrbit H) (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H P.x Y) :
    ∀ d ∈ windingInterval (linearizedXiPath H P Y), 1 < d := by sorry

end HryniewiczCriterion
