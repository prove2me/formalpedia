-- Prove2me | Theorems.Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul
-- name    : Module.End.exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/d180244c-6afc-5034-85f8-b66556829b1b
-- title:
--   Joint eigenvectors exist iff joint dual eigenvectors exist
-- statement:
--   Let $K$ be a field and $V$ a finite-dimensional $K$-vector space, let $\iota$ be an arbitrary index type, let $T : \iota \to \operatorname{End}_K(V)$ be a family of endomorphisms that commute pairwise (i.e. $T_i T_j = T_j T_i$ for all $i, j$), and let $\mu : \iota \to K$ be a family of scalars. The assertion is the equivalence of two existence statements: on the one hand there is a vector $v \in V$ with $v \neq 0$ and $T_i v = \mu_i v$ for every $i$; on the other hand there is a functional $\varphi$ in the dual space $\operatorname{Hom}_K(V,K)$ with $\varphi \neq 0$ and $(T_i)^{\vee}\varphi = \mu_i \varphi$ for every $i$, where $(T_i)^{\vee}$ denotes the transpose of $T_i$, so that the condition reads $\varphi \circ T_i = \mu_i \varphi$. Thus the eigensystem $(\mu_i)_i$ is realised by a joint eigenvector of the family $(T_i)_i$ precisely when it is realised by a joint eigenvector of the transposed family.
--
--   A statement of linear algebra for a commuting family of operators, allowing an eigensystem detected on a dual space (for instance on a space of functionals given by Hecke-type pairings) to be transported back to the space itself. It is used in the project by `Module.End.exists_eigenvector_or_exists_eigenvector_of_dualMap_apply_eq_smul`'s companion result [`Module.End.exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul`](thm.html#Module.End.exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.End.exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι : Type*} (T : ι → Module.End K V) (hT : ∀ i j, Commute (T i) (T j)) (μ : ι → K) :
    (∃ v : V, v ≠ 0 ∧ ∀ i, T i v = μ i • v) ↔
      ∃ φ : Module.Dual K V, φ ≠ 0 ∧ ∀ i, (T i).dualMap φ = μ i • φ := by sorry
