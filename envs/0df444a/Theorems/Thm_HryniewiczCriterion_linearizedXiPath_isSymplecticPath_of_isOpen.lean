-- Prove2me | Theorems.Thm_HryniewiczCriterion_linearizedXiPath_isSymplecticPath_of_isOpen
-- name    : HryniewiczCriterion.linearizedXiPath_isSymplecticPath_of_isOpen
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T17:01:26.499998+00:00
-- url     : https://prove2.me/theorems/5517d2a2-bca1-4eac-8cf1-da22e17c95ba
-- title:
--   The contact-plane path is a smooth path in $SL(2,\mathbb{R})$ (local smoothness version)
-- statement:
--   Let $H:\mathbb{R}^4\to\mathbb{R}$ be smooth on an open set $U$, and let $P=(x,T)$ be a periodic orbit of $X_H$ on $H^{-1}(1)$ with $x(t)\in U$ and $dH(x(t))\,x(t)>0$ for all $t$. Let $Y$ be the linearized flow along $x$. Then the path $\varphi$ of $P$ is a smooth path in $SL(2,\mathbb{R})$ on $[0,1]$ with $\varphi(0)=I$. Here $\varphi$ is the linearized Reeb flow on $\xi$, written in the global frame $Z_1,Z_2$.
--
--   This generalizes the statement for globally smooth $H$ (`linearizedXiPath_isSymplecticPath`). It applies, for example, to a $2$-homogeneous convex model, which is smooth only away from the origin.
-- source:
--   Hryniewicz, https://arxiv.org/html/1105.2077v5, Section 2.1.1, equations (4)–(5), frame of Section 3 (p. 12); generalization of the platform theorem `HryniewiczCriterion.linearizedXiPath_isSymplecticPath` to Hamiltonians smooth near the orbit.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.linearizedXiPath_isSymplecticPath_of_isOpen (H : R4 → ℝ) (U : Set R4) (hU : IsOpen U)
    (hH : ContDiffOn ℝ ∞ H U) (P : PeriodicOrbit H) (hxU : ∀ t, P.x t ∈ U)
    (hpos : ∀ t, 0 < fderiv ℝ H (P.x t) (P.x t))
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H P.x Y) :
    ContDiffOn ℝ ∞ (fun t i j => linearizedXiPath H P Y t i j) (Set.Icc 0 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, (linearizedXiPath H P Y t).det = 1) ∧
      linearizedXiPath H P Y 0 = 1 := by sorry
