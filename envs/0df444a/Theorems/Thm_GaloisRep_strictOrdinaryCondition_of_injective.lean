-- Prove2me | Theorems.Thm_GaloisRep_strictOrdinaryCondition_of_injective
-- name    : GaloisRep.strictOrdinaryCondition_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/1fb3c91b-6646-513a-971f-55bb336c26e3
-- title:
--   Strict ordinarity descends along injective local homomorphisms
-- statement:
--   Let $A$ and $B$ be commutative local rings, both algebras over a commutative ring $\mathcal O$, and let $\varphi : A \to B$ be an injective local ring homomorphism. Let $\rho$ be an object of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), that is, a free finite $A$-module $V$ with $\operatorname{rank}_A V = 2$ together with a monoid homomorphism $\rho$ from $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (the automorphism group of `AlgebraicClosure ℚ` over $\mathbb Q$) to $\operatorname{End}_A V$ which is continuous for the maximal-ideal-adic topology in the sense that for each $n$ some finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ has all its fixing automorphisms acting trivially modulo $\mathfrak m_A^n V$. Let $p$ be a prime with $p \neq 2$, let $S$ be a finite set of natural numbers, and assume $p$ is nilpotent in $B$. Assume the base change $B \otimes_A V$ of $\rho$ along $\varphi$ (with $\sigma$ acting by $\rho(\sigma) \otimes 1$) satisfies [`GaloisRep.strictOrdinaryCondition 𝒪 p S`](def/GaloisRep_StrictOrdinary.html#L28). Then $\rho$ itself satisfies that condition over $A$, namely: (i) $p \in \mathfrak m_A$ and for all $n$, all $\sigma$ and all $a$ such that $\sigma$ acts as $\mu \mapsto \mu^a$ on the $p^n$-th roots of unity, $\det \rho(\sigma) - a \in (p^n)$; (ii) $p \in \mathfrak m_A$ and for every valuation subring $P$ of $\overline{\mathbb Q}$ lying over $p$ there is a submodule $L \subseteq V$ which is the $A$-span of the first member of some basis indexed by `Fin 2`, stable under the decomposition subgroup of $P$, satisfying $\rho(\sigma)v - v \in L$ for all $\sigma$ in the inertia subgroup and all $v \in V$, and such that each $\sigma$ in the decomposition subgroup admits $x, z \in A$ with $\rho(\sigma)w = xw$ for $w \in L$, $\rho(\sigma)v - zv \in L$ for all $v \in V$, and $x - a z \in (p^n)$ whenever $\sigma$ acts as $\mu \mapsto \mu^a$ on the $p^n$-th roots of unity; and (iii) for every prime $q \notin S$ and every valuation subring lying over $q$, the inertia subgroup acts trivially.
--
--   This is the closure under injective local homomorphisms (Mazur's subobject clause) for the strict ordinary local condition: strict ordinarity of a deformation is detected after an injective base change whenever $p$ is nilpotent downstream. It feeds into [`GaloisRep.isDeformationCondition_strictOrdinaryCondition`](thm.html#GaloisRep.isDeformationCondition_strictOrdinaryCondition), the verification that the strict ordinary condition is a deformation condition in the sense used for the modularity-lifting argument; the ordinary line over $A$ is produced by [`GaloisRep.ordinaryCondition_of_injective`](thm.html#GaloisRep.ordinaryCondition_of_injective), and its uniqueness comes from the residual ramification at $p$ forced by the cyclotomic determinant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_strictOrdinaryCondition_of_injective.lean

import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.strictOrdinaryCondition_of_injective
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (hinj : Function.Injective φ) (ρ : GaloisRepAdic A)
    {p : ℕ} {S : Finset ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hnB : IsNilpotent (p : B))
    (h : GaloisRep.strictOrdinaryCondition 𝒪 p S (ρ.baseChangeAlong φ hφ)) :
    GaloisRep.strictOrdinaryCondition 𝒪 p S ρ := by sorry
