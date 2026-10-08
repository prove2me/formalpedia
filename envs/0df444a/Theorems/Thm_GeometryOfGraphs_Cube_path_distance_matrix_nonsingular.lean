-- Prove2me | Theorems.Thm_GeometryOfGraphs_Cube_path_distance_matrix_nonsingular
-- name    : GeometryOfGraphs.Cube.path_distance_matrix_nonsingular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:56.641427+00:00
-- url     : https://prove2.me/theorems/fcbd1d8d-ab4e-46b7-b716-60344b4bb7ed
-- title:
--   Proof of Proposition 5.10 — path distance matrix is nonsingular
-- statement:
--   Let $m\geq2$ and index a path's vertices by $0,\ldots,m-1$. Its distance matrix $D$, with $D_{rs}=|r-s|$, has nonzero determinant:
--
--   $$
--   \det\bigl(|r-s|\bigr)_{0\leq r,s<m}\ne0.
--   $$
--
--   The paper cites this fact in the rank lower bound for even cycles. The $m=1$ matrix is zero and is excluded.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 233, proof of Proposition 5.10, citing [44] pp. 64–65; https://doi.org/10.1007/BF01200757

import Mathlib

set_option autoImplicit false

namespace GeometryOfGraphs.Cube

/-- The distance matrix of a path with at least two vertices is nonsingular. -/
theorem path_distance_matrix_nonsingular (m : ℕ) (hm : 2 ≤ m) :
    (Matrix.of (fun r s : Fin m =>
      |((r : ℕ) : ℝ) - ((s : ℕ) : ℝ)|)).det ≠ 0 := by sorry

end GeometryOfGraphs.Cube
