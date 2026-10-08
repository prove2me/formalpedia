-- Prove2me | Theorems.Thm_HryniewiczCriterion_homogFrame_symplectic_det_pos
-- name    : HryniewiczCriterion.homogFrame_symplectic_det_pos
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T20:03:15.151987+00:00
-- url     : https://prove2.me/theorems/9281ee9a-f391-4681-a378-be66fa23375a
-- title:
--   The frame $F(y)$ is symplectic and $i\,\delta(F(y))$ lies in the right half-plane
-- statement:
--   Let $H:\mathbb{R}^4\to\mathbb{R}$ and $y\in\mathbb{R}^4$ with $dH(y)\,y>0$. Let $F(y)$ be the frame matrix with columns
--   $$y,\quad X_H(y)/\omega_0(y,X_H(y)),\quad Z_1(y),\quad Z_2(y),$$
--   and let $\delta=\det\,\texttt{graphBasis4}$ be the graph determinant. Then $F(y)$ preserves $\omega_0$, and
--   $$\operatorname{Re}\bigl(i\,\delta(F(y))\bigr)>0 .$$
--
--   So $\delta(F(y))$ stays in a fixed open half-plane for every admissible base point $y$. Along any loop of base points $y=x(t)$, the argument of $\delta(F(x(t)))$ therefore has zero total change: the frame loop contributes nothing to determinant angles.
-- source:
--   Frame of Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, (3.35)–(3.36), p. 220; explicit computation.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.homogFrame_symplectic_det_pos (H : R4 → ℝ) (y : R4)
    (hy : 0 < fderiv ℝ H y y) :
    (∀ u v : R4, omega0 ((homogFrame H y).mulVec u) ((homogFrame H y).mulVec v) = omega0 u v) ∧
      0 < (Complex.I * (graphBasis4 (homogFrame H y)).det).re := by sorry
