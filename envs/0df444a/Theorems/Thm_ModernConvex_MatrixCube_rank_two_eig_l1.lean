-- Prove2me | Theorems.Thm_ModernConvex_MatrixCube_rank_two_eig_l1
-- name    : ModernConvex.MatrixCube.rank_two_eig_l1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:47.990021+00:00
-- url     : https://prove2.me/theorems/b585805c-7b0c-46dc-b386-6e360231afa2
-- title:
--   Lemma 4.4.5 — ‖λ(fgᵀ + gfᵀ)‖₁ = 2‖f‖₂‖g‖₂
-- statement:
--   Let $f,g\in\mathbb R^n$ and $A=fg^T+gf^T$. Then
--   $$\|\lambda(A)\|_1=2\|f\|_2\|g\|_2 ,$$
--   where $\|\lambda(A)\|_1$ is the sum of the absolute values of the eigenvalues of the symmetric matrix $A$ and $\|\cdot\|_2$ is the Euclidean norm.
--
--   The lemma turns the spectral expression (4.4.49) into the small semidefinite program (4.4.50) when the matrices $A_i[x]$ have the rank-two form $a_i[x]b_i^T+b_ia_i^T[x]$, as in the interval Lyapunov problem.
--
--   **Formalization Note** $fg^T$ is Mathlib's `vecMulVec f g`, and $\|f\|_2=\sqrt{\sum_if_i^2}$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 197, Lemma 4.4.5

import Mathlib
import Definitions.Def_ModernConvex_MatrixCube_MatrixCube

open Matrix

namespace ModernConvex.MatrixCube

/-- Ben-Tal–Nemirovski, Lemma 4.4.5, p. 197: for vectors `f, g ∈ ℝⁿ` and `A = fgᵀ + gfᵀ`,
`‖λ(A)‖₁ = 2‖f‖₂‖g‖₂`, where `‖λ(A)‖₁` is the sum of the absolute values of the eigenvalues
of the symmetric matrix `A` and `‖·‖₂` is the Euclidean norm. -/
theorem rank_two_eig_l1 {n : ℕ} (f g : Fin n → ℝ) :
    eigL1 (vecMulVec f g + vecMulVec g f) =
      2 * Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := by sorry

end ModernConvex.MatrixCube
