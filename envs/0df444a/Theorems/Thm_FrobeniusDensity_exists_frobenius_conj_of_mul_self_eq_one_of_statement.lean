-- Prove2me | Theorems.Thm_FrobeniusDensity_exists_frobenius_conj_of_mul_self_eq_one_of_statement
-- name    : FrobeniusDensity.exists_frobenius_conj_of_mul_self_eq_one_of_statement
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/dd73a90b-b5d4-583e-ac6b-82558d85580d
-- title:
--   Involutions in G_ℚ are Frobenius conjugates on finite levels
-- statement:
--   Assume the following density hypothesis: for every number field $M$ that is Galois over $\mathbb Q$ the predicate [`FrobeniusDensity.Statement M`](def/TaylorWiles_Primes.html#L72) holds, i.e. for every $\sigma\in\mathrm{Gal}(M/\mathbb Q)$ and every finite set $S$ of natural numbers there is an $\ell\notin S$ satisfying `RealizesCyclicAt M σ ℓ`: $\ell$ is prime and for every prime ideal $Q$ of $\mathcal O_M$ lying over [`FrobeniusDensity.ratPrimeIdeal ℓ`](def/TaylorWiles_Primes.html#L42) with finite residue ring there is a $k$ coprime to the order of $\sigma$ such that $\sigma^{k}$ is conjugate in $\mathrm{Gal}(M/\mathbb Q)$ to the arithmetic Frobenius `arithFrobAt ℤ (M ≃ₐ[ℚ] M) Q`. Let $L$ be an intermediate field of $\mathbb Q\subset\overline{\mathbb Q}=$ `AlgebraicClosure ℚ` with $[L:\mathbb Q]$ finite, let $\sigma$ be a $\mathbb Q$-algebra automorphism of $\overline{\mathbb Q}$ with $\sigma\sigma=1$, and let $S$ be a finite set of natural numbers. Then there exist a prime $\ell\notin S$, a valuation subring $A$ of $\overline{\mathbb Q}$ and automorphisms $\tau,\gamma$ of $\overline{\mathbb Q}$ over $\mathbb Q$ such that $\ell$ is a non-unit of $A$, $\tau$ lies in the decomposition subgroup of $A$ over $\mathbb Q$ and acts on the residue field of $A$ by $x\mapsto x^{\ell}$, and $\sigma x=(\gamma\tau\gamma^{-1})x$ for every $x\in L$.
--
--   This is the involution case of the qualitative Frobenius density statement in the form needed for Galois-theoretic arguments over $\overline{\mathbb Q}$: an element of order dividing $2$, such as a complex conjugation, agrees on any prescribed finite level $L$ with a conjugate of an honest Frobenius element at a prime outside a prescribed finite set. It is used in the selection of auxiliary primes with prescribed Frobenius trace for an elliptic curve, in [`WeierstrassCurve.exists_prime_isGoodPrimeFor_dvd_apOfModel_dvd_add_one`](thm.html#WeierstrassCurve.exists_prime_isGoodPrimeFor_dvd_apOfModel_dvd_add_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusDensity_exists_frobenius_conj_of_mul_self_eq_one_of_statement.lean

import Mathlib
import Definitions.Def_TaylorWiles_Primes
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FrobeniusDensity.exists_frobenius_conj_of_mul_self_eq_one_of_statement
    (hFD : ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M], FrobeniusDensity.Statement M)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ * σ = 1) (S : Finset ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ S ∧
      ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (τ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧ ∀ x ∈ L, σ x = (γ * τ * γ⁻¹) x := by sorry
