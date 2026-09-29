-- Prove2me | Theorems.Thm_GaloisRepAdic_eq_one_of_pow_eq_one_of_coprime_of_wild_of_charpoly_map_eq
-- name    : GaloisRepAdic.eq_one_of_pow_eq_one_of_coprime_of_wild_of_charpoly_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/d8b8bdd8-3f09-5c7c-8fd6-6fccfd6dba41
-- title:
--   Wild inertia eigenvalue of order prime to q is 1
-- statement:
--   Let $A$ be a commutative noetherian local ring and let $\rho$ be an element of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), that is: a finite free $A$-module $V$ with $\operatorname{rank}_A V = 2$, a monoid homomorphism $\rho.\rho$ from the group of field automorphisms of $\overline{\mathbb Q}$ over $\mathbb Q$ to $\operatorname{End}_A(V)$, subject to the adic continuity condition that for every $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ such that every automorphism fixing $L$ pointwise moves each $v \in V$ only inside $\mathfrak m^n \cdot V$, where $\mathfrak m$ is the maximal ideal of $A$. Assume $p$ is prime with the image of $p$ in $A$ lying in $\mathfrak m$, $q$ is a prime different from $p$, and $P$ is a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $P$. Let $\sigma$ be an automorphism of $\overline{\mathbb Q}/\mathbb Q$ which is wild at $P$ in the sense that $\sigma(z)z^{-1} - 1$ is a non-unit of $P$ for every $z \neq 0$. Let $B$ be a commutative domain, $j : A \to B$ an injective ring homomorphism, and $a \in B^\times$ a unit such that the image under $j$ of the characteristic polynomial of $\rho.\rho(\sigma)$ equals $(X - a)(X - a^{-1})$ in $B[X]$. If $a^n = 1$ for some natural number $n$ coprime to $q$, then $a = 1$.
--
--   This is the eigenvalue form of the statement that an element of wild inertia above $q$ acts through a group of $q$-power order in an $\mathfrak m$-adically continuous two-dimensional representation, the residue characteristic $p$ being different from $q$. It is used in the analysis of the characteristic polynomial of inertia for the two-dimensional representations attached to newforms, in the two statements [`CuspForm.IsNewform.exists_charpoly_inertia_eq_and_pow_sub_one_ne_one_of_forall_linearMap_psCarrier_eq_zero_of_factorization_eq_two_of_irreducible_odd_of_ne_two`](thm.html#CuspForm.IsNewform.exists_charpoly_inertia_eq_and_pow_sub_one_ne_one_of_forall_linearMap_psCarrier_eq_zero_of_factorization_eq_two_of_irreducible_odd_of_ne_two) and its variant with the extra hypothesis on the value $-1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_eq_one_of_pow_eq_one_of_coprime_of_wild_of_charpoly_map_eq.lean

import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem GaloisRepAdic.eq_one_of_pow_eq_one_of_coprime_of_wild_of_charpoly_map_eq
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A)
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits)
    {B : Type} [CommRing B] [IsDomain B] (j : A →+* B) (hj : Function.Injective j)
    (a : Bˣ) (ha : (LinearMap.charpoly (ρ.ρ σ)).map j = (X - C ((a : Bˣ) : B)) * (X - C (((a⁻¹ : Bˣ) : B))))
    {n : ℕ} (hn : n.Coprime q) (han : a ^ n = 1) :
    a = 1 := by sorry
