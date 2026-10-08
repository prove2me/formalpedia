-- Prove2me | Theorems.Thm_HryniewiczCriterion_linearizedFlow_solution_eq
-- name    : HryniewiczCriterion.linearizedFlow_solution_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T17:01:32.809225+00:00
-- url     : https://prove2.me/theorems/46d21a2f-1128-44de-bbd4-908ff2796308
-- title:
--   Solutions of the linearized Hamiltonian equation are given by the linearized flow
-- statement:
--   Let $H$ be smooth on an open set $U\subset\mathbb{R}^4$, $x:\mathbb{R}\to U$ a curve, and $Y$ the linearized flow along $x$: $Y(0)=I$, $Y'=DX_H(x)\,Y$. If $w$ solves $w'(t)=DX_H(x(t))\,w(t)$ for all $t$, then $w(t)=Y(t)\,w(0)$.
--
--   The proof needs no Grönwall estimate. $\omega_0(Y(t)u,w(t))$ is constant, and $Y(t)$ is symplectic, hence invertible.
-- source:
--   Standard uniqueness for linear ODEs, here derived from the symplectic structure; used for the invariant splitting of Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, (3.34)–(3.36), p. 220.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.linearizedFlow_solution_eq (H : R4 → ℝ) (U : Set R4) (hU : IsOpen U)
    (hH : ContDiffOn ℝ ∞ H U) (x : ℝ → R4) (hxU : ∀ t, x t ∈ U)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y) (w : ℝ → R4)
    (hw : ∀ t, HasDerivAt w (fderiv ℝ (hamiltonianVectorField H) (x t) (w t)) t) (t : ℝ) :
    w t = Y t (w 0) := by sorry
