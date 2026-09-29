-- Prove2me | Theorems.Thm_Matrix_exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero
-- name    : Matrix.exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/50487b2d-4900-5076-847d-76df2fc6d01c
-- title:
--   Iwasawa decomposition of GLₙ(ℝ): A = b o
-- statement:
--   For every natural number $n$ and every $n \times n$ real matrix $A$ (indexed by `Fin n`) whose determinant is non-zero, there exist real $n \times n$ matrices $b$ and $o$ with the following four properties: $b_{ij} = 0$ whenever $j < i$, that is, $b$ is upper triangular; $b_{ii} > 0$ for every index $i$, that is, the diagonal entries of $b$ are strictly positive; for all indices $i,j$ one has $\sum_{a} o_{ai} o_{aj} = 1$ if $i = j$ and $0$ otherwise, i.e. the columns of $o$ are orthonormal for the standard inner product, equivalently $o^{\mathsf T} o = 1$ and $o$ is orthogonal; and $A = b\,o$. Only existence of such a factorisation is asserted: no uniqueness, and no continuity or smoothness in $A$, is claimed. Orthogonality of $o$ is recorded as the explicit entrywise sum rather than through any group-theoretic structure, and the factors appear in the order 'triangular times orthogonal'.
--
--   This is the Iwasawa (or $QR$, Gram–Schmidt) decomposition $GL_n(\mathbb{R}) = B^{+} \cdot O(n)$, with $B^{+}$ the upper triangular matrices with positive diagonal entries, in the form $A = b\,o$. It serves as a linear-algebra tool in the cubic-induction arguments of the Langlands–Tunnell part of the development, where it is used to normalise a basis so that certain orthogonality and leading-coefficient relations can be read off.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    ∃ b o : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j : Fin n, j < i → b i j = 0) ∧ (∀ i : Fin n, 0 < b i i) ∧
      (∀ i j : Fin n, ∑ a : Fin n, o a i * o a j = if i = j then 1 else 0) ∧ A = b * o := by sorry
