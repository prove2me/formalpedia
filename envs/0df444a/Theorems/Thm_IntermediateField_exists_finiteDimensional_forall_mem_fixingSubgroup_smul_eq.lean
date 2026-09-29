-- Prove2me | Theorems.Thm_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq
-- name    : IntermediateField.exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/a3059772-59c6-5909-a910-979bcb550d87
-- title:
--   Units of an algebraic extension are fixed by a finite-level subgroup
-- statement:
--   Let $K$ and $\Omega$ be fields with $\Omega$ a $K$-algebra that is algebraic over $K$, and let $x$ be a unit of $\Omega$, i.e. an element of the group $\Omega^{\times}$. The assertion is that there exists an intermediate field $E$ of the extension $\Omega/K$ such that $E$ is finite-dimensional as a $K$-vector space and such that, for every $K$-algebra automorphism $\sigma$ of $\Omega$ lying in the fixing subgroup of $E$ (that is, every $\sigma$ fixing each element of $E$ pointwise), one has $\sigma \bullet x = x$ in $\Omega^{\times}$, where the action is the natural action of the automorphism group on the units of $\Omega$. Thus each unit of $\Omega$ has an open stabiliser in the sense that it is fixed by the subgroup fixing some finite subextension of $K$ in $\Omega$; equivalently, $\Omega^{\times}$ is a discrete (smooth) module for $\mathrm{Aut}_K(\Omega)$ at the level of individual elements.
--
--   This is the pointwise smoothness of the multiplicative group of an algebraic extension as a module over the group of $K$-automorphisms, the coefficient module underlying Hilbert's theorem 90, the Kummer sequence and Brauer group computations. It is used to produce automorphisms fixing prescribed units, via [`IntermediateField.exists_forall_mem_fixingSubgroup_smul_eq_of_cofinal`](thm.html#IntermediateField.exists_forall_mem_fixingSubgroup_smul_eq_of_cofinal) and in the analysis of fixed elements for place decompositions over a $p$-adic algebraic closure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IntermediateField

theorem IntermediateField.exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (x : Ωˣ) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → σ • x = x := by sorry
