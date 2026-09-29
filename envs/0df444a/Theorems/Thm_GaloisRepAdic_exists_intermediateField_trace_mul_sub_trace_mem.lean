-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_intermediateField_trace_mul_sub_trace_mem
-- name    : GaloisRepAdic.exists_intermediateField_trace_mul_sub_trace_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/a525b863-4470-54d4-abf4-b9d1b912e215
-- title:
--   Traces of an adic Galois representation are locally constant modulo J
-- statement:
--   Let $R$ be a commutative local ring and let $\rho$ be a [`GaloisRepAdic R`](def/GaloisRep_Adic.html#L16), that is: a type $V$ carrying an $R$-module structure which is free and finite over $R$ with $\operatorname{rank}_R V = 2$, together with a monoid homomorphism from the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ to $\operatorname{End}_R V$, subject to the adic continuity condition [`GaloisActionIsAdicContinuous`](def/GaloisRep_Adic.html#L9): for every $n \in \mathbb{N}$ there is an intermediate field $L$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that every automorphism $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak{m}_R^n \cdot V$ for all $v \in V$ (the submodule $(\mathfrak m_R^n) \bullet \top$). Let $J$ be an ideal of $R$ for which some power $\mathfrak{m}_R^m$ of the maximal ideal is contained in $J$. The conclusion asserts the existence of an intermediate field $F$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that for all automorphisms $\sigma, \tau$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ over $\mathbb{Q}$ with $\tau$ fixing every element of $F$, one has $\operatorname{tr}\rho(\sigma\tau) - \operatorname{tr}\rho(\sigma) \in J$, where $\operatorname{tr}\rho(\cdot)$ denotes the $R$-linear trace `LinearMap.trace` of the corresponding endomorphism of $V$.
--
--   This is the statement that the trace function of a two-dimensional adically continuous Galois representation is constant modulo an $\mathfrak m$-primary ideal on cosets of an open subgroup of finite level, i.e. that $\sigma \mapsto \operatorname{tr}\rho(\sigma) \bmod J$ factors through a finite Galois level. It is used in [`GaloisRepAdic.exists_quadraticRelation_forall_of_frobenius`](thm.html#GaloisRepAdic.exists_quadraticRelation_forall_of_frobenius), where such congruences for traces are combined with the Chebotarev/Frobenius input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_intermediateField_trace_mul_sub_trace_mem.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open IsLocalRing

theorem GaloisRepAdic.exists_intermediateField_trace_mul_sub_trace_mem
    {R : Type} [CommRing R] [IsLocalRing R] (ρ : GaloisRepAdic R)
    (J : Ideal R) (hJ : ∃ m : ℕ, maximalIdeal R ^ m ≤ J) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, τ x = x) →
        ρ.trace (σ * τ) - ρ.trace σ ∈ J := by sorry
