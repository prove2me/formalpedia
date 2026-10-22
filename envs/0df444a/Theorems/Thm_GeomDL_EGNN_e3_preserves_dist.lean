-- Prove2me | Theorems.Thm_GeomDL_EGNN_e3_preserves_dist
-- name    : GeomDL.EGNN.e3_preserves_dist
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T18:14:08.997059+00:00
-- url     : https://prove2.me/theorems/2fefa223-e6e5-4eeb-a036-d612edf071c7
-- title:
--   §5.5, p. 84 — the action of E(3) leaves distances between points unchanged
-- statement:
--   Let $g \in \mathrm E(3)$ act on $\mathbb R^3$ by $\rho(g)\mathbf x = \mathbf R\mathbf x + \mathbf b$, with $\mathbf R$ a $3\times3$ orthogonal matrix and $\mathbf b\in\mathbb R^3$. Then for all $\mathbf x, \mathbf y \in \mathbb R^3$,
--   $$\|(\mathbf R\mathbf x+\mathbf b)-(\mathbf R\mathbf y+\mathbf b)\| = \|\mathbf x-\mathbf y\|,$$
--   where $\|\cdot\|$ is the Euclidean norm.
--
--   This is the fact the book invokes for the E(3) equivariance of the Satorras et al. layer: the layer sees the coordinates only through the squared distances $\|\mathbf x_u-\mathbf x_v\|^2$, which rigid motions preserve.
--
--   **Formalization Note** $\mathbf R$ ranges over `Matrix.orthogonalGroup (Fin 3) ℝ`, so reflections are included, and acts on `EuclideanSpace ℝ (Fin 3)` through `Matrix.toEuclideanLin`.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §5.5, p. 84, "the action of E(3) necessarily leaves distances between nodes unchanged"

import Mathlib
import Definitions.Def_GeomDL_EGNN_Defs

namespace GeomDL.EGNN

/-- §5.5, p. 84: "the action of E(3) necessarily leaves distances between nodes unchanged":
for every orthogonal `R ∈ O(3)` and translation `b ∈ ℝ³`, `‖(Rx + b) − (Ry + b)‖ = ‖x − y‖`. -/
theorem e3_preserves_dist (R : Matrix.orthogonalGroup (Fin 3) ℝ) (b : E3) (x y : E3) :
    ‖rigid R b x - rigid R b y‖ = ‖x - y‖ := by sorry

end GeomDL.EGNN
