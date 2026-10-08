-- Prove2me | Theorems.Thm_HryniewiczCriterion_linearizedFlow_omega0_of_isOpen
-- name    : HryniewiczCriterion.linearizedFlow_omega0_of_isOpen
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T17:01:29.574275+00:00
-- url     : https://prove2.me/theorems/a70c693f-5450-4adb-a55f-d33ffe3d38a5
-- title:
--   The linearized Hamiltonian flow preserves $\omega_0$
-- statement:
--   Let $H$ be smooth on an open set $U\subset\mathbb{R}^4$, let $x:\mathbb{R}\to U$ be any curve, and let $Y$ solve $Y(0)=I$, $Y'(t)=DX_H(x(t))\,Y(t)$. Then $Y(t)$ is symplectic for every $t$: $\omega_0(Y(t)u,Y(t)v)=\omega_0(u,v)$. The proof uses that $DX_H=J\,D^2H$ with $D^2H$ symmetric.
-- source:
--   Standard (linearized Hamiltonian flows are symplectic); used in Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, Section 3.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.linearizedFlow_omega0_of_isOpen (H : R4 → ℝ) (U : Set R4) (hU : IsOpen U)
    (hH : ContDiffOn ℝ ∞ H U) (x : ℝ → R4) (hxU : ∀ t, x t ∈ U)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y) (u v : R4) (t : ℝ) :
    omega0 (Y t u) (Y t v) = omega0 u v := by sorry
