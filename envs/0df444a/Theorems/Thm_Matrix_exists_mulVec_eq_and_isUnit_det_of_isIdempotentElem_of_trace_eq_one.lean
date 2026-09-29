-- Prove2me | Theorems.Thm_Matrix_exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one
-- name    : Matrix.exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/7c56ab46-db59-5741-bf1c-32172a6981cc
-- title:
--   Adapted basis for a trace-one 2×2 idempotent over a local ring
-- statement:
--   Let $A$ be a commutative local ring and let $e \in M_2(A)$ be a matrix indexed by `Fin 2` satisfying $e \cdot e = e$ and $\operatorname{tr} e = 1$. Then there exist two vectors $u, w \in A^2$ (functions `Fin 2 → A`) such that the matrix whose $(i,j)$ entry is the $i$-th coordinate of the $j$-th of the two vectors $u, w$ — that is, the $2\times 2$ matrix with columns $u$ and $w$ — has unit determinant, and such that $e u = u$ and $e w = 0$, the products being matrix–vector multiplication. Thus $u$ and $w$ span the two eigen-submodules of the idempotent $e$ and form a basis of $A^2$, in which $e$ becomes $\operatorname{diag}(1,0)$. The conclusion is stated in terms of unit determinant of the explicit column matrix rather than in terms of a `Basis` object.
--
--   This is the eigenbasis step in the local structure theory of a rank-two idempotent: over a local ring an idempotent of trace one splits $A^2$ into a free rank-one fixed part and a free rank-one kernel. It is used by [`LinearMap.exists_basis_apply_eq_smul_of_charpoly_map_residue_eq`](thm.html#LinearMap.exists_basis_apply_eq_smul_of_charpoly_map_residue_eq), which produces bases diagonalising a two-dimensional representation with distinct residual eigenvalues, as needed in the analysis of the action of inertia at Taylor–Wiles primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Matrix.exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one {A : Type u} [CommRing A] [IsLocalRing A]
    {e : Matrix (Fin 2) (Fin 2) A} (he : e * e = e) (htr : e.trace = 1) :
    ∃ u w : Fin 2 → A, IsUnit (Matrix.of (fun i j => ![u, w] j i)).det ∧
      e.mulVec u = u ∧ e.mulVec w = 0 := by sorry
