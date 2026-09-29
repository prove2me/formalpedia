-- Prove2me | Theorems.Thm_Matrix_existsUnique_eq_one_kroneckerMap_of_forall_commute_kroneckerMap_one
-- name    : Matrix.existsUnique_eq_one_kroneckerMap_of_forall_commute_kroneckerMap_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/74bde51f-947d-52f2-b1fe-f5c98cfb2751
-- title:
--   The commutant of M_m(K)⊗ 1 consists of 1⊗ B
-- statement:
--   Let $K$ be a commutative ring and let $m$, $n$ be finite index types with decidable equality, $m$ nonempty. Let $X$ be a square matrix over $K$ indexed by the product type $m \times n$, and suppose that for every $A \in M_m(K)$ the matrix $X$ commutes with the Kronecker product $A \otimes 1_n$, formed by `Matrix.kroneckerMap (· * ·)` so that its $((i,s),(j,t))$ entry is $A_{ij}\,(1_n)_{st}$; that is, $X \cdot (A \otimes 1_n) = (A \otimes 1_n) \cdot X$. The conclusion is that there exists a unique $B \in M_n(K)$ with $X = 1_m \otimes B$, i.e. with $X_{(i,s),(j,t)} = (1_m)_{ij} B_{st}$ for all $i,j \in m$ and $s,t \in n$. Uniqueness is asserted in the strict Lean sense: $B$ satisfies the equation, and any $B'$ satisfying it equals $B$. Only the direction stated is asserted; the converse inclusion (that every $1_m \otimes B$ commutes with every $A \otimes 1_n$) is not part of this statement.
--
--   This identifies the commutant of the subalgebra $M_m(K) \otimes 1_n$ inside $M_{m\cdot n}(K)$ as $1_m \otimes M_n(K)$, in the elementary form needed for descent of matrix identities through a Kronecker decomposition. It is used in the study of maximal orders in quaternion algebras, in the analysis of units lying in prescribed local boxes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_existsUnique_eq_one_kroneckerMap_of_forall_commute_kroneckerMap_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.existsUnique_eq_one_kroneckerMap_of_forall_commute_kroneckerMap_one
    {K : Type} [CommRing K] {m n : Type} [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n]
    (X : Matrix (m × n) (m × n) K)
    (hX : ∀ A : Matrix m m K,
      X * Matrix.kroneckerMap (· * ·) A (1 : Matrix n n K) = Matrix.kroneckerMap (· * ·) A (1 : Matrix n n K) * X) :
    ∃! B : Matrix n n K, X = Matrix.kroneckerMap (· * ·) (1 : Matrix m m K) B := by sorry
