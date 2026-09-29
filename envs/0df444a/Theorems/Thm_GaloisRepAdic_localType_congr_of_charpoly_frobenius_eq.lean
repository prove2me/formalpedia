-- Prove2me | Theorems.Thm_GaloisRepAdic_localType_congr_of_charpoly_frobenius_eq
-- name    : GaloisRepAdic.localType_congr_of_charpoly_frobenius_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/f865e5e2-a9ab-5ccb-b727-9e7e0660eced
-- title:
--   Equal Frobenius characteristic polynomials off S transport local types
-- statement:
--   Let $A$ be a commutative noetherian local ring and let $\rho_1,\rho_2$ be two objects of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), that is, each consists of a free finite $A$-module $V$ of rank $2$ together with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) = \overline{\mathbb Q}\simeq_{\mathbb Q}\overline{\mathbb Q}$ to $\mathrm{End}_A(V)$ which is adically continuous in the sense that for each $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ with $(\rho\sigma)(v)-v \in \mathfrak m_A^{\,n}\cdot V$ for all $v$ and all $\sigma$ fixing $L$ pointwise. Let $S$ be a finite set of natural numbers, and assume that for every prime $\ell \notin S$, every valuation subring $B$ of $\overline{\mathbb Q}$ with $\ell$ a nonunit of $B$, and every $\tau$ in the decomposition group of $B$ acting on the residue field of $B$ as $x \mapsto x^{\ell}$, the characteristic polynomials of $\rho_1(\tau)$ and $\rho_2(\tau)$ coincide. The conclusion is a conjunction: first, for every natural number $q$, $\rho_1$ satisfies `IsUnipotentOnInertiaAt q` if and only if $\rho_2$ does, i.e. the condition that for every valuation subring $P$ of $\overline{\mathbb Q}$ in which $q$ is a nonunit and every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$ one has $\mathrm{charpoly}(\rho(\sigma)) = (X-1)^2$ holds for one exactly when it holds for the other; second, for every natural number $q$ (including the elements of $S$), every valuation subring $B$ in which $q$ is a nonunit and every Frobenius $\tau$ at $q$ for $B$ in the above sense, the characteristic polynomials of $\rho_1(\tau)$ and $\rho_2(\tau)$ agree.
--
--   This is the transport step by which the two local invariants used in level lowering — unipotence on inertia at a prime, and the characteristic polynomial of Frobenius at a prime — are carried from one adic representation to another with the same Frobenius data outside a finite set. It is used in the comparison of the Galois representations attached to newforms with those attached to Frey curves, for instance in establishing unipotence on inertia at primes dividing the relevant parameter to first order and in the corresponding congruence statements for newforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_localType_congr_of_charpoly_frobenius_eq.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.localType_congr_of_charpoly_frobenius_eq
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ₁ ρ₂ : GaloisRepAdic A)
    (S : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ (B : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), B.LiesOverPrime ℓ → B.IsFrobeniusAt τ ℓ →
        LinearMap.charpoly (ρ₁.ρ τ) = LinearMap.charpoly (ρ₂.ρ τ)) :
    (∀ q : ℕ, ρ₁.IsUnipotentOnInertiaAt q ↔ ρ₂.IsUnipotentOnInertiaAt q) ∧
    (∀ (q : ℕ) (B : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), B.LiesOverPrime q → B.IsFrobeniusAt τ q →
        LinearMap.charpoly (ρ₁.ρ τ) = LinearMap.charpoly (ρ₂.ρ τ)) := by sorry
