-- Prove2me | Theorems.Thm_InputSparsity_Embed_coordinate_bound
-- name    : InputSparsity.Embed.coordinate_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:17:52.090795+00:00
-- url     : https://prove2.me/theorems/32dd7204-f9b4-47d9-a54e-c824be84595e
-- title:
--   §3.1, p. 8 — a unit vector's squared coordinate is bounded by leverage
-- statement:
--   Let $U\in\mathbb R^{n\times r}$ have orthonormal columns, with leverage scores $u_i=\sum_jU_{ij}^2$. Every unit vector $y$ in the column space of $U$ satisfies
--
--   $$y_i^2\le u_i\qquad(i\in[n]).$$
--
--   This coordinate bound is the input to the paper's light-coordinate concentration analysis.
--
--   **Formalization Note** Unit length is expressed by $\sum_i y_i^2=1$; the statement is independent of how the rows are ordered.
-- source:
--   Clarkson and Woodruff, Low Rank Approximation and Regression in Input Sparsity Time, arXiv:1207.6365v4, p. 8, §3.1, first paragraph

import Mathlib
import Definitions.Def_InputSparsity_Embed_SparseEmbedding

namespace InputSparsity.Embed
open Matrix

/-- Clarkson--Woodruff, §3.1, p. 8: a coordinate of a unit vector in the column space is bounded by its leverage score. -/
theorem coordinate_bound {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (hU : HasOrthonormalCols U) (y : Fin n → ℝ)
    (hy : y ∈ LinearMap.range (Matrix.mulVecLin U)) (hunit : sqNorm y = 1) :
    ∀ i : Fin n, y i ^ 2 ≤ lev U i := by sorry

end InputSparsity.Embed
