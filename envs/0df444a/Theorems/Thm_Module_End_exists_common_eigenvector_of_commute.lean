-- Prove2me | Theorems.Thm_Module_End_exists_common_eigenvector_of_commute
-- name    : Module.End.exists_common_eigenvector_of_commute
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/751b9894-1b52-5c62-ab87-53664df7e7a9
-- title:
--   Common eigenvector for a commuting family of endomorphisms
-- statement:
--   Let $K$ be an algebraically closed field and let $V$ be a nonzero finite-dimensional $K$-vector space (an additive commutative group with a $K$-module structure, assumed finite-dimensional over $K$ and nontrivial). Let $\iota$ be an arbitrary index type, with no finiteness or nonemptiness assumption, and let $T : \iota \to \operatorname{End}_K(V)$ be a family of $K$-linear endomorphisms of $V$ such that $T_i$ and $T_j$ commute for all $i, j \in \iota$, i.e. $T_i \circ T_j = T_j \circ T_i$. The assertion is that there exist a function $\chi : \iota \to K$ and a vector $v \in V$ with $v \neq 0$ such that $T_i v = \chi(i) \cdot v$ for every $i \in \iota$: the whole commuting family has a simultaneous eigenvector, with the associated system of eigenvalues recorded by $\chi$.
--
--   This is the standard simultaneous-eigenvector statement for a commuting family of endomorphisms over an algebraically closed field (the linear-algebra core of Lie's theorem in the abelian case). Within the project it is applied to families of Hecke and diamond operators, being cited in the construction of Hecke eigenvectors in group cohomology ([`CohCarrier.exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul`](thm.html#CohCarrier.exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul), [`CohCarrier.exists_isCompl_parabolicHoms_mem_invtSubmodule_heckeTL`](thm.html#CohCarrier.exists_isCompl_parabolicHoms_mem_invtSubmodule_heckeTL)) and in passing from simultaneous eigenvalue equations to eigenforms ([`CuspForm.exists_isEigenformWith_qCoeff_eq_of_heckeTLinH_eq_smul_of_heckeULinH_eq_smul_of_diamondLinH_eq_smul`](thm.html#CuspForm.exists_isEigenformWith_qCoeff_eq_of_heckeTLinH_eq_smul_of_heckeULinH_eq_smul_of_diamondLinH_eq_smul)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_exists_common_eigenvector_of_commute.lean

import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Module.End.exists_common_eigenvector_of_commute
    {K : Type*} [Field K] [IsAlgClosed K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] {ι : Type*} (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ (χ : ι → K) (v : V), v ≠ 0 ∧ ∀ i, T i v = χ i • v := by sorry
