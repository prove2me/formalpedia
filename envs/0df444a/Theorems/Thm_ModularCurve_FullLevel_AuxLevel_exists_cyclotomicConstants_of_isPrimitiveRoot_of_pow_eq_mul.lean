-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_cyclotomicConstants_of_isPrimitiveRoot_of_pow_eq_mul
-- name    : ModularCurve.FullLevel.AuxLevel.exists_cyclotomicConstants_of_isPrimitiveRoot_of_pow_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/491ede95-fc9f-562c-9aee-702bec4a7d7d
-- title:
--   Cyclotomic frame inside a general q-adic discrete valuation ring
-- statement:
--   Let $q$ and $\ell$ be primes with $5 \le q$, $3 \le \ell$ and $\ell \neq q$, let $L$ be a field of characteristic $0$, and let $\zeta, \xi \in L$ be primitive $q$-th and $q\ell$-th roots of unity. Let $A$ be a discrete valuation domain with an $A$-algebra structure on $L$ making $L$ the fraction field of $A$, assume $q$ lies in the maximal ideal of $A$, assume $\zeta$ lies in the image of $A \to L$, and let $t \in A$ satisfy $t^{q-1} = q\,w$ for some unit $w$ of $A$. The assertion is the existence of a field $L_0$ of characteristic $0$ that is a $\{q\ell\}$-cyclotomic extension of $\mathbb{Q}$, a ring homomorphism $i : L_0 \to L$, elements $\zeta_0, \xi_0 \in L_0$ that are primitive $q$-th and $q\ell$-th roots of unity with $i\zeta_0 = \zeta$ and $i\xi_0 = \xi$, and a discrete valuation domain $A_0$ with fraction field $L_0$ equipped with an algebra structure over which $A_0 \to A$ is a local homomorphism, such that: $A_0 \to A$ is injective; the square formed by $A_0 \to A \to L$ and $A_0 \to L_0 \xrightarrow{i} L$ commutes; an element $x \in L_0$ lies in the image of $A_0$ exactly when $i x$ lies in the image of $A$; $q$ lies in the maximal ideal of $A_0$; $\zeta_0$ lies in the image of $A_0$; and every generator $\varpi_0$ of the maximal ideal of $A_0$ has image $t\,w'$ in $A$ for some unit $w'$ of $A$.
--
--   This produces, inside an arbitrary characteristic-zero discrete valuation ring $A$ carrying the $q$-th and $q\ell$-th roots of unity and the element $t$ with $t^{q-1} \sim q$, the cyclotomic subframe $\mathbb{Q}(\xi) \supset A_0 = A \cap \mathbb{Q}(\xi)$ together with the comparison maps and the statement that a uniformiser of $A_0$ differs from $t$ by a unit of $A$; the last point rests on the computation $\varpi^{q-1} = \varepsilon q$ for a uniformiser of a discrete valuation ring inside a $q\ell$-th cyclotomic field over $\mathbb{Q}$. It serves as the base-change step for the identifications of completions of local rings on Drinfeld-level charts of modular curves, including their inertial level-automorphism refinement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_cyclotomicConstants_of_isPrimitiveRoot_of_pow_eq_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ModularCurve.FullLevel.AuxLevel.exists_cyclotomicConstants_of_isPrimitiveRoot_of_pow_eq_mul
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q)
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
