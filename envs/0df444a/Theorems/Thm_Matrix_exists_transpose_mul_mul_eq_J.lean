-- Prove2me | Theorems.Thm_Matrix_exists_transpose_mul_mul_eq_J
-- name    : Matrix.exists_transpose_mul_mul_eq_J
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/2a580a9a-55aa-53ed-abe6-35efce5d01ff
-- title:
--   Symplectic normal form for a unimodular alternating integer matrix
-- statement:
--   Let $n$ be a natural number and let $Q$ be a square matrix with integer entries whose rows and columns are indexed by the disjoint union $\mathrm{Fin}\,n \sqcup \mathrm{Fin}\,n$ (so $Q$ has size $2n$). Assume that $Q$ is skew-symmetric, in the strong sense that its transpose equals $-Q$ entrywise, and that its determinant is a unit of $\mathbb{Z}$, i.e. $\det Q = \pm 1$. The conclusion asserts the existence of a matrix $P$ over $\mathbb{Z}$, with the same index type $\mathrm{Fin}\,n \sqcup \mathrm{Fin}\,n$ on both sides, such that $\det P$ is a unit of $\mathbb{Z}$ and such that the congruence $P^{\mathsf T} Q P$ is exactly the standard symplectic matrix $\mathtt{Matrix.J}\,(\mathrm{Fin}\,n)\,\mathbb{Z}$, that is the block matrix with blocks $0$, $-1$ in the first row and $1$, $0$ in the second row relative to the given decomposition of the index type. Thus $Q$ is transformed into the standard alternating form on the nose, not merely up to sign or up to a permutation of the blocks, by a transformation $P$ invertible over $\mathbb{Z}$.
--
--   This is the classical statement that a unimodular alternating bilinear form on a finitely generated free $\mathbb{Z}$-module admits a symplectic basis, in matrix form over the index type $\mathrm{Fin}\,n \sqcup \mathrm{Fin}\,n$. It is used in the treatment of the intersection pairing on the homology of a curve, where it supplies the symplectic basis underlying [`AlgebraicCurve.exists_loops_pathIntegral_reciprocity`](thm.html#AlgebraicCurve.exists_loops_pathIntegral_reciprocity).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_transpose_mul_mul_eq_J.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Matrix.exists_transpose_mul_mul_eq_J {n : ℕ} (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)
    (hQ : Q.transpose = -Q) (hdet : IsUnit Q.det) :
    ∃ P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ, IsUnit P.det ∧
      P.transpose * Q * P = Matrix.J (Fin n) ℤ := by sorry
