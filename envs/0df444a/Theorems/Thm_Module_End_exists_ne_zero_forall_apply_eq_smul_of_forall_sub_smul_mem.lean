-- Prove2me | Theorems.Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem
-- name    : Module.End.exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/e55df915-1302-582f-a86f-76744a861659
-- title:
--   Joint eigenvectors lift from a quotient to the whole space
-- statement:
--   Let $K$ be a field and $V$ a finite-dimensional $K$-vector space, and let $\iota$ be an arbitrary index type. Given a family $T : \iota \to \operatorname{End}_K(V)$ of endomorphisms that commute pairwise, $T_i T_j = T_j T_i$ for all $i, j$, a $K$-subspace $W \le V$ with $T_i w \in W$ for every index $i$ and every $w \in W$, a family of scalars $\mu : \iota \to K$, and a vector $v \in V$ with $v \notin W$ such that $T_i v - \mu_i \cdot v \in W$ for every $i$ (that is, the class of $v$ in $V/W$ is a nonzero joint eigenvector of the induced operators, with eigenvalue $\mu_i$ for $T_i$), the conclusion is that there exists $u \in V$ with $u \neq 0$ and $T_i u = \mu_i \cdot u$ for every $i$: a genuine nonzero joint eigenvector in $V$ itself for the same system of eigenvalues. No assertion is made that $u$ lies outside $W$, nor that $u$ is related to $v$.
--
--   This is the standard linear-algebra pullback step for joint (generalised) eigenspaces of a commuting family of operators: a system of eigenvalues occurring on a quotient $V/W$ by a stable subspace is already realised by an eigenvector in $V$. It is used here in the proof of [`Module.End.exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul`](thm.html#Module.End.exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul), and is the mechanism by which a system of Hecke eigenvalues found on a quotient of a space of mod $p$ forms is realised by an eigenform in that space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem.lean

import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.End.exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι : Type*} (T : ι → Module.End K V) (hT : ∀ i j, Commute (T i) (T j))
    (W : Submodule K V) (hW : ∀ i, ∀ w ∈ W, T i w ∈ W)
    (mu : ι → K) (v : V) (hv : v ∉ W) (heig : ∀ i, T i v - mu i • v ∈ W) :
    ∃ u : V, u ≠ 0 ∧ ∀ i, T i u = mu i • u := by sorry
