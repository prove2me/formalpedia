-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_polarAngleLift
-- name    : HryniewiczCriterion.exists_polarAngleLift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T20:03:27.077239+00:00
-- url     : https://prove2.me/theorems/eebacddb-77e7-4302-bb1a-632323f29af3
-- title:
--   A continuous path in $SL(2,\mathbb{R})$ has a continuous polar angle
-- statement:
--   Let $\varphi:[0,1]\to SL(2,\mathbb{R})$ be continuous with $\varphi(0)=I$. Then there is a continuous function $\alpha:[0,1]\to\mathbb{R}$ with $\alpha(0)=0$ such that
--   $$\varphi(t)=R(\alpha(t))\,P(t)\qquad(t\in[0,1]),$$
--   where $R(\alpha)$ is the rotation by $\alpha$ and each $P(t)$ is symmetric positive definite.
--
--   The function $\alpha$ is the continuous rotation angle in the polar decomposition of the path. Its endpoint value $\alpha(1)$ measures the total rotation of $\varphi$ and is the quantity compared with winding numbers in Conley–Zehnder index estimates.
-- source:
--   Standard (polar decomposition in $SL(2,\mathbb{R})$); used for the rotation angle of the linearized flow in Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, pp. 221–222.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.exists_polarAngleLift (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hc : ContinuousOn (fun t i j => φ t i j) (Set.Icc 0 1))
    (hdet : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1) (h0 : φ 0 = 1) :
    ∃ α : ℝ → ℝ, IsPolarAngleLift φ α := by sorry
