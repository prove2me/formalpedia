-- Prove2me | Theorems.Thm_GaloisRepAdic_ordinaryLine_quotientScalar_sq_eq_one_of_liesOverPrime_of_liesOverPrime
-- name    : GaloisRepAdic.ordinaryLine_quotientScalar_sq_eq_one_of_liesOverPrime_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/6eb0fe95-fea6-5e00-8e4a-17cdf361f4a0
-- title:
--   Transfer of the square-one quotient scalar between places above p
-- statement:
--   Let $A$ be a commutative local ring and let $\rho$ be an object of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16): a type $V$ carrying a free finite $A$-module structure with $\mathrm{rank}_A V = 2$, a monoid homomorphism $\rho.\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) = \mathrm{AlgebraicClosure}\,\mathbb Q \simeq_{\mathbb Q} \mathrm{AlgebraicClosure}\,\mathbb Q$ to $\mathrm{End}_A V$, together with adic continuity (for every $n$ there is a finite subextension of $\overline{\mathbb Q}/\mathbb Q$ whose pointwise stabiliser moves each $v \in V$ only inside $\mathfrak m_A^n V$). Let $p$ be a prime and let $P, P'$ be valuation subrings of $\overline{\mathbb Q}$ each lying over $p$, meaning that the image of $p$ is a nonunit of the subring. Assume the hypothesis $h'$ at $P'$: for every $A$-submodule $L'$ of $V$ which is the $A$-span of the zeroth vector of some basis of $V$ indexed by $\mathrm{Fin}\ 2$, which is stable under $\rho.\rho\,\sigma$ for all $\sigma$ in the decomposition subgroup of $P'$ over $\mathbb Q$, and for which $\rho.\rho\,\sigma\,v - v \in L'$ for all $v \in V$ and all $\sigma$ in the inertia subgroup of $P'$ (viewed inside the full Galois group as the image of $P'.\mathrm{inertiaSubgroup}\ \mathbb Q$ under the inclusion of the decomposition subgroup), one has $z^2 = 1$ for every $\sigma$ in the decomposition subgroup of $P'$ and every $z \in A$ with $\rho.\rho\,\sigma\,v - z \cdot v \in L'$ for all $v$. Then the same conclusion holds at $P$: given such a line $L$ of $V$ (spanned by the zeroth vector of a basis, stable under the decomposition subgroup of $P$, with the inertia subgroup of $P$ acting trivially on $V/L$), given $\sigma$ in the decomposition subgroup of $P$ and $z \in A$ with $\rho.\rho\,\sigma\,v - z \cdot v \in L$ for all $v \in V$, one has $z \cdot z = 1$.
--
--   This is the place-independence step for the ordinary condition: since all places of $\overline{\mathbb Q}$ above $p$ are conjugate under the absolute Galois group, the statement that the scalar by which a Frobenius-type element acts on the quotient $V/L$ of an ordinary line squares to $1$ need only be checked at one such place. It is used in the passage from the ordinary condition to the strict ordinary condition for a residually trés ramifiée representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_ordinaryLine_quotientScalar_sq_eq_one_of_liesOverPrime_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.ordinaryLine_quotientScalar_sq_eq_one_of_liesOverPrime_of_liesOverPrime
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {p : ℕ} (hp : p.Prime)
    (P P' : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (hP' : P'.LiesOverPrime p)
    (h' : ∀ L' : Submodule A ρ.V, (∃ b : Module.Basis (Fin 2) A ρ.V, L' = A ∙ b 0) →
      (∀ σ ∈ P'.decompositionSubgroup ℚ, ∀ v ∈ L', ρ.ρ σ v ∈ L') →
      (∀ σ ∈ P'.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L') →
      ∀ σ ∈ P'.decompositionSubgroup ℚ, ∀ z : A,
        (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L') → z * z = 1)
    (L : Submodule A ρ.V) (hLb : ∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.decompositionSubgroup ℚ)
    (z : A) (hz : ∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) :
    z * z = 1 := by sorry
