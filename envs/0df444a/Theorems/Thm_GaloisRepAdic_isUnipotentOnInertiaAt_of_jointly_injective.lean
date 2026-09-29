-- Prove2me | Theorems.Thm_GaloisRepAdic_isUnipotentOnInertiaAt_of_jointly_injective
-- name    : GaloisRepAdic.isUnipotentOnInertiaAt_of_jointly_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/c16586a7-2aac-56a0-86ce-9bdede2d648a
-- title:
--   Unipotence on inertia descends along a jointly injective pair
-- statement:
--   Let $P$, $A$, $B$ be commutative local rings, let $\pi_A : P \to A$ and $\pi_B : P \to B$ be ring homomorphisms that are local (each carries non-units to non-units), and assume the pair is jointly injective: any $x \in P$ with $\pi_A x = 0$ and $\pi_B x = 0$ is $0$. Let $\rho$ be a [`GaloisRepAdic P`](def/GaloisRep_Adic.html#L16), that is, a free finite $P$-module $V$ with $\operatorname{rank}_P V = 2$ together with a monoid homomorphism $\rho$ from the group of $\mathbb{Q}$-automorphisms of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` to $\operatorname{End}_P V$ which is adically continuous (for each $n$ there is a finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak{m}_P^n V$ for all $v$). Fix $q \in \mathbb{N}$. Write $\rho_A$ and $\rho_B$ for the base changes of $\rho$ along $\pi_A$ and $\pi_B$, acting on $A \otimes_P V$ and $B \otimes_P V$. Assume each of $\rho_A$ and $\rho_B$ is unipotent on inertia at $q$, in the sense that for every valuation subring $\mathcal{O}$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $\mathcal{O}$ and every $\sigma$ in the image in $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $\mathcal{O}$ over $\mathbb{Q}$, the characteristic polynomial of the corresponding endomorphism is $(X-1)^2$. The conclusion is that $\rho$ itself has this property: for every such $\mathcal{O}$ and every such $\sigma$, $\operatorname{charpoly}(\rho(\sigma)) = (X-1)^2$.
--
--   This is one of the descent properties of the local deformation conditions used in the modularity-lifting argument: the condition 'unipotent on inertia at $q$', i.e. that inertia at places above $q$ acts with characteristic polynomial $(X-1)^2$, can be checked after base change along two local maps whose kernels meet in $0$. It is invoked in the verification of this condition for the $\lambda$-adic representations attached to Hecke eigenforms and for representations recognised through their Frobenius characteristic polynomials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isUnipotentOnInertiaAt_of_jointly_injective.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.isUnipotentOnInertiaAt_of_jointly_injective {P A B : Type} [CommRing P]
    [IsLocalRing P] [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (πA : P →+* A) (hπA : IsLocalHom πA) (πB : P →+* B) (hπB : IsLocalHom πB)
    (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0) (ρ : GaloisRepAdic P) {q : ℕ}
    (hA : (ρ.baseChangeAlong πA hπA).IsUnipotentOnInertiaAt q)
    (hB : (ρ.baseChangeAlong πB hπB).IsUnipotentOnInertiaAt q) :
    ρ.IsUnipotentOnInertiaAt q := by sorry
