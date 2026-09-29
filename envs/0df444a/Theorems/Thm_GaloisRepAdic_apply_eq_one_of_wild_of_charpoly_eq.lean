-- Prove2me | Theorems.Thm_GaloisRepAdic_apply_eq_one_of_wild_of_charpoly_eq
-- name    : GaloisRepAdic.apply_eq_one_of_wild_of_charpoly_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/9d795ebe-89f6-5a10-bb90-075daebd4ddf
-- title:
--   Wild inertia with unipotent characteristic polynomial acts trivially
-- statement:
--   Let $A$ be a noetherian commutative local ring, and let $\rho$ be a [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), that is: a free $A$-module $V$ of finite type with $\operatorname{rank}_A V = 2$, a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \overline{\mathbb{Q}} \simeq_{\mathrm{alg}[\mathbb{Q}]} \overline{\mathbb{Q}}$ (with $\overline{\mathbb{Q}}$ the term `AlgebraicClosure ℚ`) to $\mathrm{End}_A(V)$, together with adic continuity: for every $n$ there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that every automorphism fixing $L$ pointwise satisfies $\rho(\tau)v - v \in \mathfrak{m}_A^n \cdot V$ for all $v \in V$. Let $p$ be a prime whose image in $A$ lies in the maximal ideal, let $q$ be a prime with $q \neq p$, and let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that the image of $q$ in $\overline{\mathbb{Q}}$ is a non-unit of $P$. Let $\sigma$ be an automorphism of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ which is wild at $P$, in the sense that $\sigma(z)z^{-1} - 1$ is a non-unit of $P$ for every $z \neq 0$. If the characteristic polynomial of $\rho(\sigma)$ as an $A$-linear endomorphism of $V$ equals $(X-1)^2$, then $\rho(\sigma)$ is the identity endomorphism of $V$.
--
--   This is the standard statement that wild inertia at a prime $q$ different from the residue characteristic cannot act by a non-trivial unipotent matrix in an adically continuous two-dimensional representation, the local input used when computing the conductor of such a representation at $q$. It is used in the analysis of the inertial behaviour at $q$ of the representations attached to newforms, in the two results on characteristic polynomials of inertia elements which cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_apply_eq_one_of_wild_of_charpoly_eq.lean

import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem GaloisRepAdic.apply_eq_one_of_wild_of_charpoly_eq
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A)
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits)
    (hchar : LinearMap.charpoly (ρ.ρ σ) = (X - 1) ^ 2) :
    ρ.ρ σ = 1 := by sorry
