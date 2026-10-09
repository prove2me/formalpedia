-- Prove2me | Theorems.Thm_GaussianMatrix_schur_diag_inv
-- name    : GaussianMatrix.schur_diag_inv
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T03:40:06.82522+00:00
-- url     : https://prove2.me/theorems/012819c6-0183-4a3c-ab0c-951fada0a078
-- title:
--   Schur complement formula for a diagonal entry of $(GG^\top)^{-1}$: $((GG^\top)^{-1})_{ii} = 1/\|(I-P_i)g_i\|^2$
-- statement:
--   Let $G \in \mathbb{R}^{(n+1)\times k}$ be a real matrix, fix a row index $i \in \{0,\dots,n\}$, let $g = G_{i,:} \in \mathbb{R}^k$ be the $i$-th row of $G$, and let $H \in \mathbb{R}^{n\times k}$ be the matrix obtained from $G$ by deleting row $i$ (its rows are $G_{i',:}$, $i' \neq i$, in their original order). Assume that the Gram matrix $HH^\top \in \mathbb{R}^{n\times n}$ is invertible. Then
--
--   $$\big((GG^\top)^{-1}\big)_{ii} \;=\; \Big(g^\top g - (Hg)^\top (HH^\top)^{-1}(Hg)\Big)^{-1} \;=\; \frac{1}{\|(I-P_H)\,g\|_2^2},$$
--
--   where $P_H = H^\top (HH^\top)^{-1} H$ is the orthogonal projector of $\mathbb{R}^k$ onto the row space of $H$, so that $(I-P_H)g$ is the residual of $g$ after projection onto the span of the other rows. The quantity $g^\top g - (Hg)^\top (HH^\top)^{-1}(Hg)$ is the Schur complement of the block $HH^\top$ in $GG^\top$.
--
--   This is the deterministic linear-algebra step in the classical computation of the mean of an inverse Wishart matrix: it expresses each diagonal entry of $(GG^\top)^{-1}$ through the squared distance from one row to the span of the others, which for a Gaussian matrix has a chi-square law.
--
--   **Formalization Note.** Lean's matrix inverse is total ($A^{-1} = 0$ when $\det A = 0$) and $0^{-1} = 0$ in $\mathbb{R}$; the identity holds under the sole hypothesis $\det(HH^\top) \ne 0$, including the degenerate case where $g$ lies in the row space of $H$ (then both sides are $0$). The matrix $H$ is written `G.submatrix i.succAbove id`.
-- source:
--   standard fact (inverse of a partitioned matrix / Schur complement): for $M=\begin{pmatrix} a & b^\top \\ b & C\end{pmatrix}$ with $C$ invertible, $(M^{-1})_{11} = (a - b^\top C^{-1} b)^{-1}$; see R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge Univ. Press 2013, Section 0.7.3.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem schur_diag_inv {n k : ℕ} (G : Matrix (Fin (n + 1)) (Fin k) ℝ) (i : Fin (n + 1))
    (hH : (G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᵀ).det ≠ 0) :
    (G * Gᵀ)⁻¹ i i =
      (G i ⬝ᵥ G i - (G.submatrix i.succAbove id *ᵥ G i) ⬝ᵥ
        ((G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᵀ)⁻¹ *ᵥ
          (G.submatrix i.succAbove id *ᵥ G i)))⁻¹ := by sorry

end GaussianMatrix
