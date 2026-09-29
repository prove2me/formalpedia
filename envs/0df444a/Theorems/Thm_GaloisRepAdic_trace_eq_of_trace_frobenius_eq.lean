-- Prove2me | Theorems.Thm_GaloisRepAdic_trace_eq_of_trace_frobenius_eq
-- name    : GaloisRepAdic.trace_eq_of_trace_frobenius_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/0bd7f4ce-4b2d-5198-9cdd-07f2f89f67cb
-- title:
--   Adic traces determined by Frobenius traces outside S
-- statement:
--   Let $A$ be a noetherian local commutative ring with maximal ideal $\mathfrak m$, and let $\rho_1,\rho_2$ be two objects of type [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16): each consists of an $A$-module $V$ that is free and finite with $\operatorname{rank}_A V = 2$, a monoid homomorphism $\rho$ from the group $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ of $\mathbb Q$-algebra automorphisms of $\overline{\mathbb Q}$ to $\operatorname{End}_A V$, together with the adic continuity condition that for every $n$ there is an intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$, finite-dimensional over $\mathbb Q$, such that every automorphism fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak m^n\cdot V$ for all $v \in V$; the trace of such a representation at $\sigma$ is $\operatorname{tr}_A(\rho(\sigma)) \in A$. Let $S$ be a finite set of natural numbers, and assume that for every prime $\ell \notin S$, every valuation subring $B$ of $\overline{\mathbb Q}$ with $\ell$ a nonunit of $B$, and every automorphism $\tau$ that is a Frobenius at $\ell$ for $B$, in the sense that $\tau$ lies in the decomposition subgroup of $B$ over $\mathbb Q$ and acts on the residue field of $B$ by $x \mapsto x^{\ell}$, one has $\rho_1.\mathrm{trace}\,\tau = \rho_2.\mathrm{trace}\,\tau$. Then $\rho_1.\mathrm{trace}\,\sigma = \rho_2.\mathrm{trace}\,\sigma$ for every $\sigma \in \operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$.
--
--   This is the Chebotarev-type rigidity statement that the trace of a two-dimensional adically continuous representation over a noetherian local ring is determined by its values at Frobenius elements at primes outside a finite set. It is used in the Taylor–Wiles part of the formalisation, for instance in the analysis of the Galois representation attached to a Hecke algebra at an auxiliary prime and of its behaviour on inertia.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_trace_eq_of_trace_frobenius_eq.lean

import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.trace_eq_of_trace_frobenius_eq
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ₁ ρ₂ : GaloisRepAdic A)
    (S : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ (B : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), B.LiesOverPrime ℓ → B.IsFrobeniusAt τ ℓ →
        ρ₁.trace τ = ρ₂.trace τ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρ₁.trace σ = ρ₂.trace σ := by sorry
