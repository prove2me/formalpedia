-- Prove2me | Theorems.Thm_Module_exists_ne_zero_forall_smul_eq_smul_of_algHom
-- name    : Module.exists_ne_zero_forall_smul_eq_smul_of_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/43ed252a-e548-542e-8e8a-874a19ccc92f
-- title:
--   Characters of a faithful finite algebra have eigenvectors
-- statement:
--   Let $K$ be a field, $A$ a commutative ring carrying a $K$-algebra structure, and $V$ an abelian group equipped with both a $K$-module and an $A$-module structure, these being compatible in the sense of a scalar tower over $K$ and $A$. Assume $V$ is finite as a $K$-module, i.e. a finite-dimensional $K$-vector space, and that the action of $A$ on $V$ is faithful, that is, two elements of $A$ acting identically on every vector of $V$ are equal. Let $\chi \colon A \to K$ be a homomorphism of $K$-algebras. The assertion is that there exists $v \in V$ with $v \neq 0$ such that $a \cdot v = \chi(a) \cdot v$ for every $a \in A$, the left action being that of $A$ and the right that of $K$; thus $v$ is a simultaneous eigenvector for the whole of $A$ with system of eigenvalues given by $\chi$. Note that the nonvanishing of $V$ is not assumed separately: it follows from faithfulness together with $A$ being a nonzero ring, $A$ containing $K$ via the algebra structure.
--
--   This is the standard statement that every $K$-valued character of a commutative algebra of operators on a finite-dimensional space over which it acts faithfully is realised by a common eigenvector, in the form used by Deligne and Serre. In this development it underlies the passage from eigencharacters of Hecke algebras to actual eigenforms, and is cited by [`HeckeEis.exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1`](thm.html#HeckeEis.exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1), by the duality criterion [`Module.End.exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul`](thm.html#Module.End.exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul), and by [`Module.End.isNilpotent_of_mem_adjoin_of_forall_eigenvector_apply_eq_zero`](thm.html#Module.End.isNilpotent_of_mem_adjoin_of_forall_eigenvector_apply_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_ne_zero_forall_smul_eq_smul_of_algHom.lean

import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Algebra.Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Module.exists_ne_zero_forall_smul_eq_smul_of_algHom {K A V : Type*} [Field K] [CommRing A] [Algebra K A] [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V] [Module.Finite K V] [FaithfulSMul A V] (χ : A →ₐ[K] K) : ∃ v : V, v ≠ 0 ∧ ∀ a : A, a • v = χ a • v := by sorry
