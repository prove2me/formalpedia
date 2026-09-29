-- Prove2me | Theorems.Thm_GaloisRepAdic_isStrictOrdinaryAt_of_detIsCyclotomic_of_ordinaryLine
-- name    : GaloisRepAdic.isStrictOrdinaryAt_of_detIsCyclotomic_of_ordinaryLine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/07eb4515-f8cb-562c-a9d5-d11fa881bd6f
-- title:
--   Strict ordinarity from cyclotomic determinant and an ordinary line
-- statement:
--   Let $A$ be a noetherian commutative local ring and let $\rho$ be an adic Galois representation over $A$: a free $A$-module $V$ of rank $2$, finite over $A$, together with a monoid homomorphism $\rho.\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \mathrm{AlgebraicClosure}\,\mathbb{Q} \simeq_{\mathbb{Q}} \mathrm{AlgebraicClosure}\,\mathbb{Q}$ to $\mathrm{End}_A V$ that is continuous for the maximal-ideal-adic topology. Let $p$ be a prime and assume `ρ.DetIsCyclotomic p`: $p$ lies in the maximal ideal of $A$, and for all $n$, all $\sigma$ and all $a \in \mathbb{N}$ such that $\sigma\mu = \mu^{a}$ for every $p^n$-th root of unity $\mu$, one has $\det \rho(\sigma) - a \in (p^n)$. Let $a \in A$ with $a^2 = 1$. Assume that for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $P$ there is an $A$-submodule $L \subseteq V$ which is the span of the first vector of some $A$-basis of $V$ indexed by $\mathrm{Fin}\,2$, is stable under the decomposition subgroup of $P$, satisfies $\rho(\tau)v - v \in L$ for all $\tau$ in the inertia subgroup of $P$ (viewed inside the Galois group) and all $v \in V$, and satisfies $\rho(\sigma)v - a\,v \in L$ for every $\sigma$ acting on the residue field of $P$ by $x \mapsto x^{p}$ (Frobenius at $P$ for $p$) and all $v \in V$. The conclusion is `ρ.IsStrictOrdinaryAt p`: $p$ lies in the maximal ideal, and for every such $P$ there is a line $L$ as above, spanned by a basis vector, stable under the decomposition group, with inertia acting trivially on $V/L$, and such that for every $\sigma$ in the decomposition group there are $x, z \in A$ with $\rho(\sigma)w = x\,w$ for $w \in L$, $\rho(\sigma)v - z\,v \in L$ for all $v \in V$, and $x - a\,z \in (p^n)$ for all $n$ and $a \in \mathbb{N}$ with $\sigma\mu = \mu^{a}$ on $p^n$-th roots of unity.
--
--   This converts the local shape of a $p$-adic representation at $p$ — an ordinary line whose unramified quotient carries a Frobenius eigenvalue $a$ with $a^2 = 1$ — into the strict ordinarity condition, in which the character on the line is the product of the cyclotomic character with the character on the quotient. It is used in establishing strict ordinarity at $p$ for the representations attached to ring homomorphisms out of a Hecke algebra in the non-flat case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isStrictOrdinaryAt_of_detIsCyclotomic_of_ordinaryLine.lean

import Definitions.Def_GaloisRep_StrictOrdinary
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.isStrictOrdinaryAt_of_detIsCyclotomic_of_ordinaryLine
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (ρ : GaloisRepAdic A) {p : ℕ} (hp : p.Prime) (hdet : ρ.DetIsCyclotomic p)
    (a : A) (ha : a ^ 2 = 1)
    (hline : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∃ L : Submodule A ρ.V,
        (∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0) ∧
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
        (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ τ v - v ∈ L) ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
          ∀ v : ρ.V, ρ.ρ σ v - a • v ∈ L)) :
    ρ.IsStrictOrdinaryAt p := by sorry
