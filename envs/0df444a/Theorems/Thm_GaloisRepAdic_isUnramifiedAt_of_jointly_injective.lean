-- Prove2me | Theorems.Thm_GaloisRepAdic_isUnramifiedAt_of_jointly_injective
-- name    : GaloisRepAdic.isUnramifiedAt_of_jointly_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/f2e1e1a1-91f5-5104-8def-b3f8969966eb
-- title:
--   Unramifiedness descends along a jointly injective pair of local maps
-- statement:
--   Let $P$, $A$, $B$ be commutative local rings and let $\pi_A : P \to A$, $\pi_B : P \to B$ be ring homomorphisms, each assumed local (non-units are carried to non-units). Assume the pair is jointly injective: an element $x \in P$ with $\pi_A(x) = 0$ and $\pi_B(x) = 0$ is zero. Let $\rho$ be a [`GaloisRepAdic P`](def/GaloisRep_Adic.html#L16), that is, a finite free $P$-module $V$ of rank $2$ together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the automorphism group of `AlgebraicClosure ℚ` over $\mathbb{Q}$) to $\mathrm{End}_P(V)$ satisfying the adic continuity condition [`GaloisActionIsAdicContinuous`](def/GaloisRep_Adic.html#L9), and let $q$ be a natural number. Suppose the base change of $\rho$ along $\pi_A$ and the base change along $\pi_B$ (the representations on $A \otimes_P V$ and $B \otimes_P V$ given by $\sigma \mapsto (\rho(\sigma))\otimes \mathrm{id}$) are both unramified at $q$, in the sense that for every valuation subring $\mathcal{O}$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $\mathcal{O}$ and every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $\mathcal{O}$ over $\mathbb{Q}$, the base-changed operator is the identity. Then $\rho$ itself is unramified at $q$ in the same sense: each such $\sigma$ acts on $V$ as the identity.
--
--   This is the fibre-product (and, in the diagonal case of a single injective map, the sub-object) clause for the unramified condition among Mazur's axioms for a local deformation condition, here for the conjunct 'unramified at $q$' alone. It is used by [`GaloisRepAdic.flatCondition_of_jointly_injective`](thm.html#GaloisRepAdic.flatCondition_of_jointly_injective), [`GaloisRep.ordinaryCondition_of_injective`](thm.html#GaloisRep.ordinaryCondition_of_injective) and [`GaloisRep.ordinaryCondition_of_jointly_injective`](thm.html#GaloisRep.ordinaryCondition_of_jointly_injective), where the same descent is assembled for the flat and ordinary conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isUnramifiedAt_of_jointly_injective.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.isUnramifiedAt_of_jointly_injective {P A B : Type} [CommRing P]
    [IsLocalRing P] [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (πA : P →+* A) (hπA : IsLocalHom πA) (πB : P →+* B) (hπB : IsLocalHom πB)
    (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0) (ρ : GaloisRepAdic P) {q : ℕ}
    (hA : (ρ.baseChangeAlong πA hπA).IsUnramifiedAt q)
    (hB : (ρ.baseChangeAlong πB hπB).IsUnramifiedAt q) : ρ.IsUnramifiedAt q := by sorry
