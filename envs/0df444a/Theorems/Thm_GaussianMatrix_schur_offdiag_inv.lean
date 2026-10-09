-- Prove2me | Theorems.Thm_GaussianMatrix_schur_offdiag_inv
-- name    : GaussianMatrix.schur_offdiag_inv
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T06:17:45.159987+00:00
-- url     : https://prove2.me/theorems/8c61c1a9-4c1d-4898-a4da-83895bfb3e5e
-- title:
--   Partitioned inverse, off-diagonal row entries: $((GG^\top)^{-1})_{i,j} = -\big((HH^\top)^{-1}Hg\big)_{j}\,((GG^\top)^{-1})_{ii}$
-- statement:
--   Let $G \in \mathbb{R}^{(n+1)\times k}$, fix a row index $i$, let $g = G_{i,:}$ be the $i$-th row and $H \in \mathbb{R}^{n\times k}$ the matrix of the remaining rows in their original order, and assume $HH^\top$ is invertible. Let $c = (HH^\top)^{-1}Hg \in \mathbb{R}^n$ be the least-squares coefficients of $g$ on the rows of $H$. Then for every $a \in \{1,\dots,n\}$, writing $i \oplus a$ for the index in $G$ of the $a$-th row of $H$,
--
--   $$\big((GG^\top)^{-1}\big)_{i,\,i\oplus a} \;=\; -\,c_a\,\big((GG^\top)^{-1}\big)_{ii}.$$
--
--   Together with the diagonal formula $((GG^\top)^{-1})_{ii} = 1/(g^\top g - (Hg)^\top(HH^\top)^{-1}Hg)$ (`schur_diag_inv`), this describes the whole $i$-th row of $(GG^\top)^{-1}$: it equals $Q^{-1}(1, -c^\top)$ (in the ordering $i$ first), with $Q$ the Schur complement. It is the deterministic step that turns off-diagonal entries of an inverse Wishart matrix into a ratio of independent quantities (regression coefficients over a residual).
--
--   **Formalization Note.** The index $i\oplus a$ is `i.succAbove a` and $H$ is `G.submatrix i.succAbove id`. Lean's matrix inverse is total; the identity holds under the sole hypothesis $\det(HH^\top)\ne 0$, including the degenerate case $Q = 0$, where $GG^\top$ is singular and both sides are $0$.
-- source:
--   standard fact (inverse of a partitioned matrix): for $M=\begin{pmatrix} a & b^\top \\ b & C\end{pmatrix}$ with $C$ invertible and $s = a - b^\top C^{-1}b \ne 0$, the first row of $M^{-1}$ is $s^{-1}\,(1,\,-b^\top C^{-1})$; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge Univ. Press 2013, Section 0.7.3.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem schur_offdiag_inv {n k : ℕ} (G : Matrix (Fin (n + 1)) (Fin k) ℝ) (i : Fin (n + 1))
    (a : Fin n)
    (hH : (G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᵀ).det ≠ 0) :
    (G * Gᵀ)⁻¹ i (i.succAbove a) =
      -(((G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᵀ)⁻¹ *ᵥ
          (G.submatrix i.succAbove id *ᵥ G i)) a) * (G * Gᵀ)⁻¹ i i := by sorry

end GaussianMatrix
