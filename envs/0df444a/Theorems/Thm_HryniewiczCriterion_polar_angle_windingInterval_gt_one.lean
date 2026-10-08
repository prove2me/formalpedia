-- Prove2me | Theorems.Thm_HryniewiczCriterion_polar_angle_windingInterval_gt_one
-- name    : HryniewiczCriterion.polar_angle_windingInterval_gt_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T15:22:59.23398+00:00
-- url     : https://prove2.me/theorems/f8db6526-c2d2-4998-b391-ae3e559b61b0
-- title:
--   Polar-angle criterion for winding above one in $SL(2,\mathbb{R})$
-- statement:
--   Let $\varphi:[0,1]\to SL(2,\mathbb{R})$ be smooth with $\varphi(0)=I$, and let $\alpha$ be its continuous polar angle: $\varphi(t)=R(\alpha(t))P(t)$ with $P(t)$ symmetric positive definite and $\alpha(0)=0$. Let $\lambda_1,\lambda_2$ be the eigenvalues of the graph unitary $W(\Gamma_{\varphi(1)})W(\Delta)^{-1}$ in $(\mathbb{R}^2\oplus\mathbb{R}^2,-\omega_0\oplus\omega_0)$, and $\operatorname{ang}(\lambda)\in(0,2\pi]$ their arguments with $\operatorname{ang}(1)=2\pi$. If
--   $$2\,\alpha(1)\;\ge\;4\pi+\operatorname{ang}(\lambda_1)+\operatorname{ang}(\lambda_2),$$
--   then every vector turns strictly more than once under $\varphi$: the winding interval $I(\varphi)$ lies in $(1,\infty)$.
--
--   This is the two-dimensional index computation behind HWZ (3.45)–(3.46), in the lower semicontinuous convention of Hryniewicz (5): it converts a bound on the polar angle of the contact path into the winding bound that characterizes Conley–Zehnder index at least three.
-- source:
--   Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, proof of Theorem 3.4, (3.45)–(3.46), p. 222, in the winding-interval form of Hryniewicz, https://arxiv.org/html/1105.2077v5, Section 2.1.1, equations (4)–(5). Reduction lemma; not a verbatim numbered assertion.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.polar_angle_windingInterval_gt_one (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hφ : ContDiffOn ℝ ∞ (fun t i j => φ t i j) (Set.Icc 0 1))
    (hsymp : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1) (h0 : φ 0 = 1)
    (α : ℝ → ℝ) (hα : IsPolarAngleLift φ α)
    (h : 4 * Real.pi + eigenAngleSum (graphUnitary2 (φ 1)) ≤ 2 * α 1) :
    ∀ d ∈ windingInterval φ, 1 < d := by sorry
