-- Prove2me | Theorems.Thm_Module_End_exists_forall_apply_eq_smul_of_pairwise_commute
-- name    : Module.End.exists_forall_apply_eq_smul_of_pairwise_commute
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/942171c8-c3b4-513c-93e5-90e11e0721cc
-- title:
--   Common eigenvector for a commuting family of endomorphisms
-- statement:
--   Let $K$ be an algebraically closed field and let $V$ be a $K$-vector space which is finite-dimensional over $K$ and nontrivial (so $V \neq 0$). Let $\iota$ be an arbitrary index type, with no finiteness or nonemptiness assumption, and let $T : \iota \to \operatorname{End}_K(V)$ be a family of $K$-linear endomorphisms of $V$ which commute pairwise in the sense of `Pairwise`, i.e. $T_i T_j = T_j T_i$ for all $i \neq j$ (the diagonal case being automatic). The conclusion is that there exists a vector $v \in V$ with $v \neq 0$ such that for every index $i$ there is a scalar $c \in K$ with $T_i v = c \cdot v$; that is, the family has a common eigenvector, the eigenvalue being allowed to depend on $i$ and being produced existentially rather than as a function of $i$.
--
--   This is the standard fact that a pairwise commuting family of endomorphisms of a nonzero finite-dimensional vector space over an algebraically closed field admits a simultaneous eigenvector. It is used to produce normalised Hecke eigenforms, via [`CuspForm.exists_isNormalizedEigenform`](thm.html#CuspForm.exists_isNormalizedEigenform) and [`CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul`](thm.html#CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul), and in the construction of a ring homomorphism out of a corner ring in [`CohCarrier.exists_ringHom_cornerRing_heckeT_eq_smul_of_idempotentSplitting`](thm.html#CohCarrier.exists_ringHom_cornerRing_heckeT_eq_smul_of_idempotentSplitting).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_exists_forall_apply_eq_smul_of_pairwise_commute.lean

import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Module.End.exists_forall_apply_eq_smul_of_pairwise_commute
    {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V]
    {ι : Type*} (T : ι → Module.End K V) (hT : Pairwise fun i j ↦ Commute (T i) (T j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v := by sorry
