-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_isClosed_posSemidef
-- name    : ModernConvex.Relaxations.isClosed_posSemidef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:51:12.8376+00:00
-- url     : https://prove2.me/theorems/6c048234-8dbb-45be-8997-c47347476cc4
-- title:
--   The positive semidefinite cone is closed
-- statement:
--   **The cone of positive semidefinite matrices is closed.**
--
--   For $X\succeq0$ if and only if $X$ is symmetric and $v^{\mathsf T}Xv\ge0$ for every $v$. Hence
--   $$\{X : X\succeq0\}=\{X : X=X^{\mathsf T}\}\cap\bigcap_{v\in\mathbb R^n}\{X : v^{\mathsf T}Xv\ge0\}.$$
--   The first set is closed because $X\mapsto X^{\mathsf T}$ and $X\mapsto X$ are continuous and $\mathbb R^{n\times n}$ is Hausdorff; each set in the intersection is closed because $X\mapsto v^{\mathsf T}Xv=\sum_{i,j}v_iX_{ij}v_j$ is a polynomial, hence continuous, in the entries of $X$. An arbitrary intersection of closed sets is closed, so the cone is closed.
--
--   This is the closedness that, together with boundedness (`|X_ij| ≤ 1` for unit-diagonal $X\succeq0$), makes the primal body $\{X\succeq0,\ X_{ii}=1\}$ compact — the hypothesis of the ellipsoid method. Mathlib has no closedness statement for `PosSemidef`; the quadratic-form characterisation avoids any use of eigenvalue continuity.
-- source:
--   The quadratic-form characterisation of positive semidefiniteness (Ben-Tal & Nemirovski, (4.3.15) discussion, p. 170); the closedness hypothesis of Bubeck arXiv:1405.4980v2, Thm 2.4, p. 250.

import Mathlib

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **The positive semidefinite cone is closed.** -/
theorem isClosed_posSemidef {n : ℕ} :
    IsClosed {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} := by sorry

end ModernConvex.Relaxations
