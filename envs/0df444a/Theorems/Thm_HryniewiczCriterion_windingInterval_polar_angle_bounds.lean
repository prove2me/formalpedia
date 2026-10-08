-- Prove2me | Theorems.Thm_HryniewiczCriterion_windingInterval_polar_angle_bounds
-- name    : HryniewiczCriterion.windingInterval_polar_angle_bounds
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T16:12:44.427278+00:00
-- url     : https://prove2.me/theorems/48fb6703-44a8-4b7c-b525-bfd371692691
-- title:
--   Winding numbers versus the polar rotation angle of a path in $SL(2,\mathbb{R})$
-- statement:
--   Let $\varphi:[0,1]\to M_2(\mathbb{R})$ have a continuous polar angle $\alpha$: $\alpha(0)=0$ and $\varphi(t)=R(\alpha(t))P(t)$ with $P(t)$ symmetric positive definite. Suppose $\varphi(1)=R(\alpha(1))P$ with $\det P=1$. Then every element $d$ of the winding interval $I(\varphi)$ (total rotation, in turns, of a vector $e^{is}$ under $\varphi$) satisfies
--   $$\bigl|2\pi d-\alpha(1)\bigr|<\frac{\pi}{2},\qquad 2\pi d\;\ge\;\alpha(1)-\arccos\frac{2}{\operatorname{tr}P}.$$
--   The first bound holds because the angle between $P(t)v$ and $v$ stays in $(-\pi/2,\pi/2)$. The second comes from the sharp bound on that angle when $\det P=1$.
-- source:
--   Hryniewicz, https://arxiv.org/html/1105.2077v5, Section 2.1.1, winding interval (4); polar decomposition estimate used in Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, (3.45)–(3.46), p. 222. Elementary comparison lemma; not a verbatim numbered assertion.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.windingInterval_polar_angle_bounds {φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {α : ℝ → ℝ}
    (hα : IsPolarAngleLift φ α) {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.PosDef)
    (hdet : P.det = 1) (hφ1 : φ 1 = rotationMatrix (α 1) * P) :
    ∀ d ∈ windingInterval φ,
      α 1 - Real.arccos (2 / (P 0 0 + P 1 1)) ≤ 2 * Real.pi * d ∧
        |2 * Real.pi * d - α 1| < Real.pi / 2 := by sorry
