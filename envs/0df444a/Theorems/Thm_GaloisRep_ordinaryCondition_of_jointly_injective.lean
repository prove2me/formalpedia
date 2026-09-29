-- Prove2me | Theorems.Thm_GaloisRep_ordinaryCondition_of_jointly_injective
-- name    : GaloisRep.ordinaryCondition_of_jointly_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/8a1336c0-4c62-5538-8c92-bfc4e71fed41
-- title:
--   Ordinary condition descends along a jointly injective pair
-- statement:
--   Let $P$, $A$, $B$ be commutative local rings, let $\mathcal{O}$ be a commutative ring with algebra structures on $P$, $A$ and $B$, and let $\pi_A : P \to A$ and $\pi_B : P \to B$ be ring homomorphisms that are local (non-units are sent to non-units), jointly injective in the sense that $\pi_A x = 0$ and $\pi_B x = 0$ force $x = 0$. Let $\rho$ be a [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16) over $P$: a free $P$-module $V$ of rank $2$, finite over $P$, with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (realised as the $\mathbb{Q}$-automorphisms of `AlgebraicClosure ℚ`) to $\mathrm{End}_P(V)$ which is continuous for the $\mathfrak{m}_P$-adic topology, meaning that for every $n$ some finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ has the property that elements fixing $L$ pointwise act trivially modulo $\mathfrak{m}_P^n V$. Let $p$ be a prime with $p \neq 2$, nilpotent in $A$ and in $B$, and let $S$ be a finite set of natural numbers. Assume both base changes $A \otimes_P V$ and $B \otimes_P V$, with the Galois action obtained by base change of each $\rho(\sigma)$ along $\pi_A$ respectively $\pi_B$, satisfy [`GaloisRep.ordinaryCondition 𝒪 p S`](def/GaloisRep_LocalConditions.html#L28), i.e. (i) $p$ lies in the maximal ideal and for all $n$, $\sigma$ and $a$ with $\sigma\mu = \mu^a$ for every $p^n$-th root of unity $\mu$, one has $\det \rho(\sigma) \equiv a \pmod{p^n}$; (ii) at every valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ there is a line spanned by the first vector of some basis which is stable under the decomposition group and on which the inertia subgroup acts trivially in the quotient, i.e. $\rho(\sigma)v - v$ lies in it for all $v$ and all $\sigma$ in inertia; (iii) $\rho$ is unramified at every prime $q \notin S$, in the sense that inertia at every valuation subring over $q$ acts trivially. Then $\rho$ itself satisfies [`GaloisRep.ordinaryCondition 𝒪 p S`](def/GaloisRep_LocalConditions.html#L28).
--
--   This is the descent-along-a-jointly-injective-pair property of the ordinary local condition, the form in which one verifies Mazur's axiom for a deformation condition when $P$ is a fibre product $A \times_C B$ of coefficient rings. It feeds into [`GaloisRep.isDeformationCondition_ordinaryCondition`](thm.html#GaloisRep.isDeformationCondition_ordinaryCondition) and into the corresponding statement for the strict ordinary condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_ordinaryCondition_of_jointly_injective.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.ordinaryCondition_of_jointly_injective
    {P A B : Type} [CommRing P] [IsLocalRing P] [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 P] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (πA : P →+* A) (hπA : IsLocalHom πA) (πB : P →+* B) (hπB : IsLocalHom πB)
    (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0) (ρ : GaloisRepAdic P) {p : ℕ} {S : Finset ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hnA : IsNilpotent (p : A)) (hnB : IsNilpotent (p : B))
    (hA : GaloisRep.ordinaryCondition 𝒪 p S (ρ.baseChangeAlong πA hπA))
    (hB : GaloisRep.ordinaryCondition 𝒪 p S (ρ.baseChangeAlong πB hπB)) :
    GaloisRep.ordinaryCondition 𝒪 p S ρ := by sorry
