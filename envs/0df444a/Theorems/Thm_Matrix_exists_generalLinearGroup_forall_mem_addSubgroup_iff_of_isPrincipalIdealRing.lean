-- Prove2me | Theorems.Thm_Matrix_exists_generalLinearGroup_forall_mem_addSubgroup_iff_of_isPrincipalIdealRing
-- name    : Matrix.exists_generalLinearGroup_forall_mem_addSubgroup_iff_of_isPrincipalIdealRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/e29348fc-0c84-5e69-b48b-ec43c8c4ef70
-- title:
--   Bounded full lattices of matrices over a PID are principal
-- statement:
--   Let $R$ be a principal ideal domain with fraction field $K$ (via an $R$-algebra structure on $K$ making it the fraction ring of $R$), and let $n$ be a finite index type. Let $L$ be an additive subgroup of the matrix ring $M_n(K)$ subject to three hypotheses: (i) $L$ is stable under right multiplication by integral matrices, i.e. $x \cdot \iota(m) \in L$ for all $x \in L$ and all $m \in M_n(R)$, where $\iota$ denotes entrywise application of the structure map $R \to K$; (ii) $L$ is bounded, i.e. there is $d \in R$, $d \neq 0$, such that for every $x \in L$ and all indices $i, j$ the entry $\iota(d)\, x_{ij}$ lies in the image of $R \to K$; (iii) $L$ is full, i.e. there is $N \in R$, $N \neq 0$, such that $\iota(N) \cdot \iota(m) \in L$ for every $m \in M_n(R)$. The conclusion asserts the existence of $g \in \mathrm{GL}_n(K)$ such that for every $x \in M_n(K)$ one has $x \in L$ if and only if all entries of $g^{-1}x$ lie in the image of $R$ in $K$; that is, $L = g\,M_n(R)$.
--
--   This is the statement that a bounded full right $M_n(R)$-submodule of $M_n(K)$ over a principal ideal domain $R$ is principal, the matrix-ring form of the fact that a lattice in $K^n$ over a PID is free with a basis that is a $K$-basis. It is used in the treatment of maximal orders in quaternion algebras, where it supplies the local generator at each finite place in [`QuaternionAlgebra.IsMaximalOrder.exists_ofFiniteIdele_eq_of_forall_mul_mem`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_ofFiniteIdele_eq_of_forall_mul_mem) and its variant for indefinite algebras ramified at a prescribed set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_generalLinearGroup_forall_mem_addSubgroup_iff_of_isPrincipalIdealRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.exists_generalLinearGroup_forall_mem_addSubgroup_iff_of_isPrincipalIdealRing
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (L : AddSubgroup (Matrix n n K))
    (hmul : ∀ x ∈ L, ∀ m : Matrix n n R, x * m.map (algebraMap R K) ∈ L)
    (hbdd : ∃ d : R, d ≠ 0 ∧ ∀ x ∈ L, ∀ i j, algebraMap R K d * x i j ∈ (algebraMap R K).range)
    (hfull : ∃ N : R, N ≠ 0 ∧ ∀ m : Matrix n n R, algebraMap R K N • m.map (algebraMap R K) ∈ L) :
    ∃ g : GL n K, ∀ x : Matrix n n K,
      x ∈ L ↔ ∀ i j, (((g⁻¹ : GL n K) : Matrix n n K) * x) i j ∈ (algebraMap R K).range := by sorry
