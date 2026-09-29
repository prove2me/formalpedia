-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_charpoly_eq_twist
-- name    : GaloisRepAdic.exists_charpoly_eq_twist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/25adce7d-4b51-5864-89ff-668ca718dcc6
-- title:
--   Twisting a two-dimensional adic Galois representation by a character
-- statement:
--   Let $A$ be a commutative local ring and let $\rho$ be an element of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), that is: a type $V$ carrying an $A$-module structure which is free and finite with $\operatorname{rank}_A V = 2$, together with a monoid homomorphism $\rho.\rho$ from $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ (the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`) to $\operatorname{End}_A(V)$ satisfying [`GaloisActionIsAdicContinuous`](def/GaloisRep_Adic.html#L9): for every $n$ there is an intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$, finite-dimensional over $\mathbb Q$, such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak m^n \cdot V$ for all $v \in V$, where $\mathfrak m$ is the maximal ideal of $A$. Let $\theta$ be a monoid homomorphism from the same automorphism group to $A^{\times}$ for which there exists a finite-dimensional intermediate field $L$ with $\theta(\sigma) = 1$ whenever $\sigma$ fixes $L$ pointwise. The conclusion is that there exists $\rho'$ again in [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16) such that for every $\sigma$ the characteristic polynomial of $\rho'(\sigma)$ equals $X^2 - \theta(\sigma)\operatorname{tr}(\rho(\sigma))X + \theta(\sigma)^2\det(\rho(\sigma))$.
--
--   This is the existence of the twist $\rho \otimes \theta$ of a two-dimensional adic Galois representation by a character of finite level, recorded through the effect of the twist on characteristic polynomials. It is used in the construction, from a newform, of a representation whose inertial characteristic polynomials are expressed via the cyclotomic character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_charpoly_eq_twist.lean

import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem GaloisRepAdic.exists_charpoly_eq_twist
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (θ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (hθ : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) → θ σ = 1) :
    ∃ ρ' : GaloisRepAdic A, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.charpoly (ρ'.ρ σ) =
        X ^ 2 - C (((θ σ : Aˣ) : A) * LinearMap.trace A ρ.V (ρ.ρ σ)) * X
          + C (((θ σ : Aˣ) : A) ^ 2 * LinearMap.det (ρ.ρ σ)) := by sorry
