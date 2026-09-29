-- Prove2me | Theorems.Thm_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq
-- name    : IntermediateField.exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/abb37e20-6167-58a2-a858-c73a02390eb4
-- title:
--   Every element of an algebraic extension has an open stabiliser
-- statement:
--   Let $K$ and $\Omega$ be fields with $\Omega$ a $K$-algebra which is algebraic over $K$, and let $x \in \Omega$. The assertion is that there exists an intermediate field $E$ of the extension $\Omega/K$, that is, a $K$-subalgebra of $\Omega$ closed under inverses, such that $\Omega$'s subextension $E$ is finite-dimensional as a $K$-vector space and such that every $K$-algebra automorphism $\sigma$ of $\Omega$ lying in the fixing subgroup of $E$ — the subgroup of those automorphisms fixing each element of $E$ — satisfies $\sigma x = x$. No separability, normality or finiteness assumption is placed on $\Omega/K$ beyond algebraicity, and the intermediate field $E$ is produced existentially rather than named in the statement.
--
--   This is the pointwise statement that the natural action of the group of $K$-automorphisms of $\Omega$ on $\Omega$ is continuous for the Krull topology: each element of $\Omega$ has stabiliser containing the fixing subgroup of a finite subextension, so the stabiliser is open. It is used in the multiplicative form [`IntermediateField.exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq`](thm.html#IntermediateField.exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq), which records the same property for a scalar action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IntermediateField

theorem IntermediateField.exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (x : Ω) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → σ x = x := by sorry
