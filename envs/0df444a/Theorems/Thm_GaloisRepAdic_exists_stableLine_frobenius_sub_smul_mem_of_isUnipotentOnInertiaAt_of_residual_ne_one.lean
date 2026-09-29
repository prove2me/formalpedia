-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_stableLine_frobenius_sub_smul_mem_of_isUnipotentOnInertiaAt_of_residual_ne_one
-- name    : GaloisRepAdic.exists_stableLine_frobenius_sub_smul_mem_of_isUnipotentOnInertiaAt_of_residual_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/4206d682-5bba-57d4-8770-f08a723321ce
-- title:
--   Rank-one inertia coinvariants with scalar Frobenius action
-- statement:
--   Let $A$ be a reduced commutative local ring and let $\rho$ be an element of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16): a free finite $A$-module $V = \rho.V$ with $\operatorname{rank}_A V = 2$, together with a monoid homomorphism $\rho.\rho$ from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{End}_A(V)$ that is continuous for the $\mathfrak m$-adic filtration (for each $n$ there is a finite extension $L/\mathbb Q$ in $\overline{\mathbb Q}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak m^n V$ for all $v$). Let $q$ be a natural number and assume `IsUnipotentOnInertiaAt`: for every valuation subring of $\overline{\mathbb Q}$ in which $q$ is a non-unit, every element of the inertia subgroup (the image in $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ of the inertia subgroup inside the decomposition subgroup) acts on $V$ with characteristic polynomial $(X-1)^2$. Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit in $P$, and let $\tau_0$ lie in the inertia subgroup of $P$ and act non-trivially on the residual representation $\mathrm{ResidueField}(A)\otimes_A V$. Then there are a submodule $L \subseteq V$ and $u \in A$ such that: $L = A\,b_0$ for some $A$-basis $(b_0,b_1)$ of $V$; $L$ is the supremum over $\tau$ in the inertia subgroup of $P$ of the ranges of $\rho(\tau)-1$; $L$ is stable under the decomposition subgroup of $P$; inertia acts trivially on $L$; $\rho(\tau)v - v \in L$ for all inertia elements $\tau$ and all $v \in V$; and for every $\sigma$ lying in the decomposition subgroup of $P$ and inducing $x\mapsto x^q$ on the residue field of $P$, one has $\rho(\sigma)v - u\,v \in L$ for all $v \in V$.
--
--   This is the structure theorem for the inertia coinvariants of a rank-two representation over a reduced local ring at a prime where inertia acts unipotently but non-trivially residually: the coinvariants $V/L$ are free of rank one and Frobenius acts on them by the scalar $u$, as used in Darmon–Diamond–Taylor §4.2 to see that the operator $U_q$ lies in the anemic Hecke algebra. It is cited by [`CuspForm.heckeLocal.exists_forall_point_apply_eq_qCoeff_of_not_isUnramifiedAt`](thm.html#CuspForm.heckeLocal.exists_forall_point_apply_eq_qCoeff_of_not_isUnramifiedAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_stableLine_frobenius_sub_smul_mem_of_isUnipotentOnInertiaAt_of_residual_ne_one.lean

import Mathlib
import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.exists_stableLine_frobenius_sub_smul_mem_of_isUnipotentOnInertiaAt_of_residual_ne_one
    {A : Type} [CommRing A] [IsLocalRing A] [IsReduced A]
    (ρ : GaloisRepAdic A) (q : ℕ) (hunip : ρ.IsUnipotentOnInertiaAt q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (τ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ₀ : τ₀ ∈ P.inertiaSubgroupIn ℚ)
    (hτ₀' : ρ.residual.ρ τ₀ ≠ 1) :
    ∃ (L : Submodule A ρ.V) (u : A),
      (∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0) ∧
      (⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ τ - 1)) = L ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v ∈ L, ρ.ρ τ v = v) ∧
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ τ v - v ∈ L) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
        ∀ v : ρ.V, ρ.ρ σ v - u • v ∈ L) := by sorry
