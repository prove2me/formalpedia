-- Prove2me | Theorems.Thm_GaloisRepAdic_apply_eq_one_of_mem_inertiaSubgroupIn_of_wild
-- name    : GaloisRepAdic.apply_eq_one_of_mem_inertiaSubgroupIn_of_wild
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/44ba691e-0cc6-5466-b971-13189a6c1630
-- title:
--   Wild inertia at q ≠ p acts trivially
-- statement:
--   Let $R$ be a commutative noetherian local ring with maximal ideal $\mathfrak{m}$, and let $\rho$ be an element of [`GaloisRepAdic R`](def/GaloisRep_Adic.html#L16): a finite free $R$-module $V$ with $\operatorname{rank}_R V = 2$, together with a monoid homomorphism $\rho.\rho$ from $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, to $\operatorname{End}_R V$, which is $\mathfrak{m}$-adically continuous in the sense that for every $n$ there is a finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ with $\rho(\tau)v - v \in \mathfrak{m}^n \cdot V$ for all $\tau$ fixing $L$ pointwise and all $v \in V$. Let $p$ be a prime whose image in $R$ lies in $\mathfrak{m}$, and let $q$ be a prime with $q \neq p$. Assume the residual representation $\rho.\mathrm{residual}$, namely the base change $\mathrm{ResidueField}(R) \otimes_R V$ with $\tau$ acting by $\rho(\tau) \otimes 1$, is unramified at $q$: for every valuation subring $A$ of $\overline{\mathbb{Q}}$ in which $q$ is a non-unit and every $\tau$ in the image in $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$, the residual action of $\tau$ is the identity. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ in which $q$ is a non-unit, and let $\sigma$ lie in the image in $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$ and satisfy the wildness condition that $\sigma(z) z^{-1} - 1$ is a non-unit of $P$ for every $z \neq 0$. Then $\rho.\rho\,\sigma$ is the identity endomorphism of $V$.
--
--   This is the local statement underlying Lemma 2.44 of Darmon–Diamond–Taylor: wild inertia at $q$ is pro-$q$, whereas an element acting trivially on the residual representation acts at each finite level through a pro-$p$ kernel of reduction, so with $q \neq p$ it must act trivially. It is used in the construction of the inertia character attached to an adic representation with cyclotomic determinant at a prime of the required shape.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_apply_eq_one_of_mem_inertiaSubgroupIn_of_wild.lean

import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsLocalRing Polynomial

theorem GaloisRepAdic.apply_eq_one_of_mem_inertiaSubgroupIn_of_wild
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ρ : GaloisRepAdic R) {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ maximalIdeal R) {q : ℕ} (hq : q.Prime)
    (hqp : q ≠ p) (hunr : ρ.residual.IsUnramifiedAt q) (P : ValuationSubring (AlgebraicClosure ℚ))
    (hP : P.LiesOverPrime q) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ)
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) :
    ρ.ρ σ = 1 := by sorry
