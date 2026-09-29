-- Prove2me | Theorems.Thm_GaloisRepAdic_detIsCyclotomic_baseChangeAlong
-- name    : GaloisRepAdic.detIsCyclotomic_baseChangeAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/f9fe2a15-7d7e-5e5a-82ce-96c010aacccd
-- title:
--   Cyclotomic determinant is preserved under local base change
-- statement:
--   Let $A$ and $B$ be commutative local rings and let $\varphi\colon A\to B$ be a ring homomorphism which is local, i.e. carries non-units to non-units. Let $\rho$ be an object of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16): a free $A$-module $V$ of finite type with $\operatorname{finrank}_A V = 2$, together with a monoid homomorphism $\rho$ from the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ to $\operatorname{End}_A V$ which is adically continuous in the sense that for every $n$ there is a finite extension $L/\mathbb{Q}$ inside $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak{m}_A^n\cdot V$ for all $v \in V$. Assume `ρ.DetIsCyclotomic p` for a natural number $p$, that is: $p$ lies in the maximal ideal of $A$, and for all $n \in \mathbb{N}$, all $\sigma$ and all $a \in \mathbb{N}$, if $\sigma\mu = \mu^a$ for every $\mu$ with $\mu^{p^n} = 1$, then $\det \rho(\sigma) - a \in (p^n)A$. The conclusion is that the base change `ρ.baseChangeAlong φ hφ` — the representation on $B \otimes_A V$, with $B$ an $A$-algebra via $\varphi$ and each $\rho(\sigma)$ replaced by its base change — satisfies `DetIsCyclotomic p` over $B$: $p \in \mathfrak{m}_B$, and the same congruence for $\det$ modulo $(p^n)B$.
--
--   This records that the condition "the determinant of the representation is the $p$-adic cyclotomic character" is stable under extension of the coefficient ring along a local homomorphism, one of the requirements for the ordinary deformation conditions to cut out subfunctors of the deformation functor. It is used wherever a representation satisfying the local conditions is pushed forward along a local map of coefficient rings, for instance to a quotient of a universal deformation ring or to a Hecke algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_detIsCyclotomic_baseChangeAlong.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.detIsCyclotomic_baseChangeAlong
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {p : ℕ} (h : ρ.DetIsCyclotomic p) : (ρ.baseChangeAlong φ hφ).DetIsCyclotomic p := by sorry
