-- Prove2me | Theorems.Thm_IsCyclotomicExtension_exists_isUnit_pow_sub_one_eq_mul_natCast_of_isDiscreteValuationRing
-- name    : IsCyclotomicExtension.exists_isUnit_pow_sub_one_eq_mul_natCast_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/626e5690-80ce-5696-b2df-f83175232334
-- title:
--   Ramification of q in ℚ(ζ_{qℓ}): varpi^{q-1}=ε q
-- statement:
--   Let $q$ and $\ell$ be primes with $q \neq \ell$, and let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $\{q\ell\}$, that is, $L$ is generated over $\mathbb{Q}$ by a primitive $q\ell$-th root of unity. Let $A$ be a commutative domain which is a discrete valuation ring, equipped with an algebra structure over which $L$ is a fraction field of $A$. Assume that the image of $q$ in $A$ lies in the maximal ideal $\mathfrak{m}_A$ of $A$ (so that the valuation of $A$ is the one attached to a prime of $L$ above $q$), and let $\varpi \in A$ be an element generating $\mathfrak{m}_A$, i.e. $\mathfrak{m}_A = (\varpi)$. The conclusion is that there is a unit $\varepsilon \in A$ with $\varpi^{q-1} = \varepsilon \cdot q$, the exponent being the natural-number difference $q-1$. Equivalently, the image of $q$ in $A$ has valuation exactly $q-1$: the ramification index of the chosen prime of $\mathbb{Q}(\zeta_{q\ell})$ above $q$ equals $q-1$.
--
--   This records the classical ramification computation in $\mathbb{Q}(\zeta_{q\ell})$, where $q$ ramifies with index $q-1$ coming from the $\mathbb{Q}(\zeta_q)$ part while the $\ell$-part is unramified at $q$, in the form of an explicit factorisation of $q$ by a power of a uniformiser. It is used in the construction of auxiliary full-level structures on modular curves, supplying the relation between a uniformiser and $q$ needed there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsCyclotomicExtension_exists_isUnit_pow_sub_one_eq_mul_natCast_of_isDiscreteValuationRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsCyclotomicExtension.exists_isUnit_pow_sub_one_eq_mul_natCast_of_isDiscreteValuationRing
    (q ℓ : ℕ) [Fact q.Prime] [Fact ℓ.Prime] (hqℓ : q ≠ ℓ)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    ∃ ε : A, IsUnit ε ∧ ϖ ^ (q - 1) = ε * (q : A) := by sorry
