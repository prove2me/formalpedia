-- Prove2me | Theorems.Thm_IsCyclotomicExtension_exists_isUnit_natCast_eq_mul_uniformizer_pow_sub_one
-- name    : IsCyclotomicExtension.exists_isUnit_natCast_eq_mul_uniformizer_pow_sub_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/ddafc36c-479c-554c-819c-48745c59500d
-- title:
--   Total ramification: p = u varpiᵖ⁻¹ in a DVR containing ζₚ
-- statement:
--   Let $p$ be a natural number that is prime, and let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, with $\zeta \in L$ a primitive $p$-th root of unity. Let $A$ be a commutative domain which is a discrete valuation ring, equipped with an algebra structure over which $L$ is its field of fractions. Assume that the image of $p$ in $A$ lies in the maximal ideal $\mathrm{IsLocalRing.maximalIdeal}\ A$, and that $\zeta$ lies in the image of $A$, i.e. there exists $z \in A$ with $\mathrm{algebraMap}\ A\ L\ z = \zeta$. Let $\varpi \in A$ be such that the maximal ideal of $A$ equals the principal ideal $(\varpi)$, i.e. $\varpi$ is a uniformiser. The conclusion is that there exists a unit $u \in A^\times$ with $(p : A) = u \cdot \varpi^{\,p-1}$, the exponent being truncated natural subtraction (so for $p = 2$ the assertion is $2 = u\varpi$).
--
--   This is the local form of the total ramification of $p$ in $\mathbb{Q}(\zeta_p)$: any uniformiser of a discrete valuation ring with fraction field $\mathbb{Q}(\zeta_p)$ containing $p$ in its maximal ideal and containing $\zeta_p$ satisfies $p = (\text{unit})\cdot\varpi^{p-1}$. It is used in the analysis of integral models of the modular curve $X_0(p)$, where the thickness of a supersingular node over such a ring must be compared with its thickness over $\mathbb{Z}_{(p)}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsCyclotomicExtension_exists_isUnit_natCast_eq_mul_uniformizer_pow_sub_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsCyclotomicExtension.exists_isUnit_natCast_eq_mul_uniformizer_pow_sub_one
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    ∃ u : Aˣ, (p : A) = ↑u * ϖ ^ (p - 1) := by sorry
