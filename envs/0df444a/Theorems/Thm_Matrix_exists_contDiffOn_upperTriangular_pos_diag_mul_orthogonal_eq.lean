-- Prove2me | Theorems.Thm_Matrix_exists_contDiffOn_upperTriangular_pos_diag_mul_orthogonal_eq
-- name    : Matrix.exists_contDiffOn_upperTriangular_pos_diag_mul_orthogonal_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/b2318283-7f21-564e-ba0f-1a40ce2029f8
-- title:
--   Smooth QR factorisation on GLₙ(ℝ)
-- statement:
--   For every natural number $n$ there exist two maps $b, o$ from the space of real $n \times n$ entry arrays $\mathrm{Fin}\,n \to \mathrm{Fin}\,n \to \mathbb{R}$ to itself with the following properties. First, both $b$ and $o$ are $C^\infty$ (differentiability exponent $\top$ in $\mathbb{N}_\infty$, i.e. of all finite orders) on the set $\{A : \det A \neq 0\}$ of arrays whose associated matrix has nonvanishing determinant. Second, for every $A$ with $\det A \neq 0$ the four assertions hold: $b(A)_{ij} = 0$ whenever $j < i$, so $b(A)$ is upper triangular; $b(A)_{ii} > 0$ for every $i$, so its diagonal entries are positive; $\sum_{a} o(A)_{ai}\, o(A)_{aj} = \delta_{ij}$ for all $i, j$, i.e. the columns of $o(A)$ are orthonormal, equivalently $o(A)^{\mathsf T} o(A) = 1$; and $A_{ij} = \sum_{k} b(A)_{ik}\, o(A)_{kj}$ for all $i, j$, i.e. $A = b(A)\, o(A)$. The values of $b$ and $o$ at singular arrays are unconstrained, and the algebraic identities are asserted only on $\{\det A \neq 0\}$.
--
--   This is the smooth dependence of the Gram–Schmidt ($QR$, or Iwasawa) factorisation $GL_n(\mathbb{R}) = B^{+} \cdot O(n)$ on the matrix, packaged as the existence of two globally defined factor maps that are infinitely differentiable on the invertible locus. It is used in the cubic-induction part of the Langlands–Tunnell argument, where smoothness at the archimedean place of functions built from an upper-triangular-equivariant datum is deduced from smoothness of the triangular and orthogonal factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_contDiffOn_upperTriangular_pos_diag_mul_orthogonal_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.exists_contDiffOn_upperTriangular_pos_diag_mul_orthogonal_eq
    (n : ℕ) :
    ∃ (b o : (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ)),
      ContDiffOn ℝ (⊤ : ℕ∞) b {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0} ∧
      ContDiffOn ℝ (⊤ : ℕ∞) o {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0} ∧
      ∀ A : Fin n → Fin n → ℝ, (Matrix.of A).det ≠ 0 →
        (∀ i j : Fin n, j < i → b A i j = 0) ∧ (∀ i : Fin n, 0 < b A i i) ∧
        (∀ i j : Fin n, ∑ a : Fin n, o A a i * o A a j = if i = j then 1 else 0) ∧
        ∀ i j : Fin n, A i j = ∑ k : Fin n, b A i k * o A k j := by sorry
