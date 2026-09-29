-- Prove2me | Theorems.Thm_FrobeniusDensity_exists_frobenius_conj_pow_of_statement
-- name    : FrobeniusDensity.exists_frobenius_conj_pow_of_statement
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/c5f47f9c-18c0-54b7-8985-d82599c72477
-- title:
--   Frobenius elements in Gal(ℚ̄/ℚ) from the density statement
-- statement:
--   Assume the hypothesis $hFD$: for every number field $M$ (a field of characteristic zero with `NumberField` instance) that is Galois over $\mathbb{Q}$, the predicate [`FrobeniusDensity.Statement M`](def/TaylorWiles_Primes.html#L72) holds, i.e. for every $\sigma \in \mathrm{Gal}(M/\mathbb{Q})$ and every finite set $S \subseteq \mathbb{N}$ there is a prime $\ell \notin S$ realising $\sigma$ cyclically at $\ell$: for every prime ideal $Q$ of $\mathcal{O}_M$ lying over the ideal $\ell\mathbb{Z}$ with finite residue ring, some power $\sigma^k$ with $k$ coprime to the order of $\sigma$ is conjugate in $\mathrm{Gal}(M/\mathbb{Q})$ to the arithmetic Frobenius at $Q$. Let $L$ be an intermediate field of $\bar{\mathbb{Q}} =$ `AlgebraicClosure ℚ` over $\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$, let $\sigma$ be a $\mathbb{Q}$-automorphism of $\bar{\mathbb{Q}}$, and let $S$ be a finite set of naturals. Then there is a prime $\ell \notin S$, a valuation subring $A$ of $\bar{\mathbb{Q}}$, automorphisms $\tau, \gamma$ of $\bar{\mathbb{Q}}$ over $\mathbb{Q}$ and a natural number $j$ such that $\ell$ is a non-unit of $A$ (that is, $A$ lies over the prime $\ell$), $\tau$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acts on the residue field of $A$ by $x \mapsto x^{\ell}$, and $\sigma x = (\gamma \tau^{j} \gamma^{-1}) x$ for all $x \in L$.
--
--   This is the passage from the Frobenius-type density statement for finite Galois number fields to a statement about the absolute Galois group of $\mathbb{Q}$: any prescribed behaviour of $\sigma$ on a fixed finite extension $L$ is matched, outside a prescribed finite set of primes, by a conjugate of a power of a genuine Frobenius element at a place of $\bar{\mathbb{Q}}$. Nothing here proves the density statement itself, which enters as a hypothesis; the result is used when Taylor–Wiles primes are chosen and when characteristic polynomials of Galois representations are compared at Frobenius elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusDensity_exists_frobenius_conj_pow_of_statement.lean

import Definitions.Def_TaylorWiles_Primes
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NumberField Pointwise

theorem FrobeniusDensity.exists_frobenius_conj_pow_of_statement
    (hFD : ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M], FrobeniusDensity.Statement M)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (S : Finset ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ S ∧
      ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (τ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (j : ℕ),
        A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧ ∀ x ∈ L, σ x = (γ * τ ^ j * γ⁻¹) x := by sorry
