-- Prove2me | Theorems.Thm_GaloisRepAdic_isOrdinaryAt_of_jointly_injective
-- name    : GaloisRepAdic.isOrdinaryAt_of_jointly_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/a466ea6f-58f6-53f6-985d-b99ed636fac9
-- title:
--   Ordinarity at odd p descends along jointly injective local maps
-- statement:
--   Let $P$, $A$, $B$ be commutative local rings and let $\pi_A : P \to A$, $\pi_B : P \to B$ be ring homomorphisms that are local (non-units go to non-units) and jointly injective, in the sense that any $x \in P$ with $\pi_A x = 0$ and $\pi_B x = 0$ vanishes. Let $\rho$ be a [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16) over $P$: a free finite $P$-module $V$ of rank $2$ together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, to $\mathrm{End}_P V$, which is adically continuous (for each $n$ there is a finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak{m}_P^n \cdot V$ for all $v$). Let $p$ be an odd prime. Assume: (i) the base change $A \otimes_P V$ along $\pi_A$ has cyclotomic determinant, i.e. $p \in \mathfrak{m}_A$ and for all $n$, all $\sigma$ and all $a \in \mathbb{N}$ with $\sigma\mu = \mu^a$ for every $p^n$-th root of unity $\mu$, one has $\det(\rho(\sigma)) - a \in (p^n)$ in $A$; (ii) the base change along $\pi_A$ is ordinary at $p$; (iii) the base change along $\pi_B$ is ordinary at $p$. Here ordinarity at $p$ of a representation over a local ring $R$ means: for every valuation subring $\mathcal{O}$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $\mathcal{O}$ there is an $R$-submodule $L$ of the underlying module which is the $R$-span of the first member of some basis indexed by $\mathrm{Fin}\,2$, is stable under the decomposition subgroup of $\mathcal{O}$ over $\mathbb{Q}$, and satisfies $\rho(\sigma)v - v \in L$ for every $\sigma$ in the image of the inertia subgroup of $\mathcal{O}$ in the decomposition subgroup and every $v$. The conclusion is that $\rho$ itself is ordinary at $p$ in this sense.
--
--   This is one of the axioms, in Mazur's sense, required of the ordinary local deformation condition at $p$: stability of the condition under descent along a pair of local homomorphisms that is injective jointly, the determinant hypothesis on one factor playing the role of $p$-distinguishedness. It is used in the construction of the ordinary deformation condition and in the criteria deducing ordinarity of an adic representation from ordinarity of its specialisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isOrdinaryAt_of_jointly_injective.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.isOrdinaryAt_of_jointly_injective {P A B : Type} [CommRing P]
    [IsLocalRing P] [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (πA : P →+* A) (hπA : IsLocalHom πA) (πB : P →+* B) (hπB : IsLocalHom πB)
    (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0) (ρ : GaloisRepAdic P) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hdetA : (ρ.baseChangeAlong πA hπA).DetIsCyclotomic p)
    (hA : (ρ.baseChangeAlong πA hπA).IsOrdinaryAt p)
    (hB : (ρ.baseChangeAlong πB hπB).IsOrdinaryAt p) : ρ.IsOrdinaryAt p := by sorry
