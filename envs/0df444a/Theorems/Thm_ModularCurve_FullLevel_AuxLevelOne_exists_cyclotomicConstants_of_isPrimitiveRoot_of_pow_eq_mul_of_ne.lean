-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_cyclotomicConstants_of_isPrimitiveRoot_of_pow_eq_mul_of_ne
-- name    : ModularCurve.FullLevel.AuxLevelOne.exists_cyclotomicConstants_of_isPrimitiveRoot_of_pow_eq_mul_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/1e42d9a2-329f-57ea-9d3c-50f08c8ae09b
-- title:
--   A cyclotomic frame inside a q-adic discrete valuation ring
-- statement:
--   Let $q$ and $\ell$ be primes with $\ell \ge 3$ and $\ell \neq q$, let $L$ be a field of characteristic zero, let $\zeta \in L$ be a primitive $q$-th root of unity and $\xi \in L$ a primitive $q\ell$-th root of unity, and let $A$ be a discrete valuation ring which is an $L$-algebra realising $L$ as its field of fractions, such that $q$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$ in $L$. Suppose further that $t \in A$ satisfies $t^{q-1} = q w$ for some unit $w$ of $A$. The assertion is the existence of a field $L_0$ of characteristic zero which is a $q\ell$-th cyclotomic extension of $\mathbb{Q}$, a ring homomorphism $i : L_0 \to L$, elements $\zeta_0, \xi_0 \in L_0$ that are primitive $q$-th and $q\ell$-th roots of unity with $i\zeta_0 = \zeta$ and $i\xi_0 = \xi$, and a discrete valuation ring $A_0$ with fraction field $L_0$, equipped with an $A_0$-algebra structure on $A$ whose structure map is a local homomorphism, such that: $A_0 \to A$ is injective; the square formed by $A_0 \to A \to L$ and $A_0 \to L_0 \xrightarrow{i} L$ commutes; an element $x \in L_0$ comes from $A_0$ precisely when $i x$ comes from $A$; $q$ lies in the maximal ideal of $A_0$; $\zeta_0$ comes from $A_0$; and every generator $\varpi_0$ of the maximal ideal of $A_0$ has image in $A$ of the form $t$ times a unit of $A$.
--
--   This manufactures, inside an arbitrary field of constants $L$ with its $q$-adic discrete valuation ring $A$, a cyclotomic subframe $(L_0,\zeta_0,\xi_0,A_0)$ over which the cyclotomic statements are formulated, together with the comparison maps and the valuation-theoretic comparison $v_A(\varpi_0) = v_A(t)$ needed to transport chart relations. It is used in the construction of ring isomorphisms for adic completions of stalks of Drinfeld charts at supersingular points, both in the plain form and in the form recording the linear part of the inertia action of level automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_exists_cyclotomicConstants_of_isPrimitiveRoot_of_pow_eq_mul_of_ne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ModularCurve.FullLevel.AuxLevelOne.exists_cyclotomicConstants_of_isPrimitiveRoot_of_pow_eq_mul_of_ne
    (q : ℕ) [Fact q.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q)
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    (t : A) (ht : ∃ w : A, IsUnit w ∧ t ^ (q - 1) = (q : A) * w) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : CharZero L₀) (_ : Algebra ℚ L₀) (_ : IsCyclotomicExtension {q * ℓ} ℚ L₀)
      (i : L₀ →+* L) (ζ₀ ξ₀ : L₀) (_ : IsPrimitiveRoot ζ₀ q) (_ : IsPrimitiveRoot ξ₀ (q * ℓ))
      (_ : i ζ₀ = ζ) (_ : i ξ₀ = ξ)
      (A₀ : Type) (_ : CommRing A₀) (_ : IsDomain A₀) (_ : IsDiscreteValuationRing A₀) (_ : Algebra A₀ L₀)
      (_ : IsFractionRing A₀ L₀) (_ : Algebra A₀ A) (_ : IsLocalHom (algebraMap A₀ A)),
      Function.Injective (algebraMap A₀ A) ∧
      (∀ a : A₀, algebraMap A L (algebraMap A₀ A a) = i (algebraMap A₀ L₀ a)) ∧

      (∀ x : L₀, (∃ a : A₀, algebraMap A₀ L₀ a = x) ↔ ∃ a : A, algebraMap A L a = i x) ∧
      ((q : A₀) ∈ IsLocalRing.maximalIdeal A₀) ∧ (∃ x : A₀, algebraMap A₀ L₀ x = ζ₀) ∧

      (∀ ϖ₀ : A₀, IsLocalRing.maximalIdeal A₀ = Ideal.span {ϖ₀} →
        ∃ w : A, IsUnit w ∧ algebraMap A₀ A ϖ₀ = t * w) := by sorry
