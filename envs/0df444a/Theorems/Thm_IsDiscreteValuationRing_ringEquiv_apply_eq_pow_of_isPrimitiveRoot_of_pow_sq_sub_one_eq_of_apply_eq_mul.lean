-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_ringEquiv_apply_eq_pow_of_isPrimitiveRoot_of_pow_sq_sub_one_eq_of_apply_eq_mul
-- name    : IsDiscreteValuationRing.ringEquiv_apply_eq_pow_of_isPrimitiveRoot_of_pow_sq_sub_one_eq_of_apply_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/89987446-732b-5012-ad8c-765082bd4840
-- title:
--   Cyclotomic action of an inertial automorphism of a DVR
-- statement:
--   Let $A$ be a commutative ring which is a domain and a discrete valuation ring, and let $q$ be a natural number carrying a `Fact` instance asserting its primality, with the image of $q$ in $A$ lying in the maximal ideal of $A$. Assume given: an element $\zeta \in A$ which is a primitive $q$-th root of unity (in the sense of Mathlib's `IsPrimitiveRoot`); an element $\pi \in A$ with $\pi^{q^2-1} = q$ in $A$; a ring automorphism $\sigma$ of $A$ (a `RingEquiv` from $A$ to itself) which is trivial on the residue field, in the sense that $\sigma a - a$ lies in the maximal ideal for every $a \in A$; an element $\alpha \in A$ with $\sigma \pi = \alpha \pi$; and a natural number $d$ such that $\alpha^{q+1} - d$ lies in the maximal ideal of $A$. The conclusion is the identity $\sigma \zeta = \zeta^{d}$ in $A$.
--
--   This is the computation of the action of an inertial automorphism on $q$-th roots of unity in terms of its tame character at a $(q^2-1)$-st root of $q$: the character $\alpha \mapsto \alpha^{q+1}$ reduces to the cyclotomic exponent modulo $q$. It is used in the analysis of the inertia action on the Drinfeld chart of the full-level modular curve, where the cyclotomic witness is matched with the linear part of a semilinear automorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_ringEquiv_apply_eq_pow_of_isPrimitiveRoot_of_pow_sq_sub_one_eq_of_apply_eq_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsDiscreteValuationRing.ringEquiv_apply_eq_pow_of_isPrimitiveRoot_of_pow_sq_sub_one_eq_of_apply_eq_mul
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (q : ℕ) [Fact q.Prime] (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (ζ : A) (hζ : IsPrimitiveRoot ζ q)
    (π : A) (hπ : π ^ (q ^ 2 - 1) = (q : A))
    (σ : A ≃+* A) (hσ : ∀ a : A, σ a - a ∈ IsLocalRing.maximalIdeal A)
    (α : A) (hσπ : σ π = α * π)
    (d : ℕ) (hd : α ^ (q + 1) - (d : A) ∈ IsLocalRing.maximalIdeal A) :
    σ ζ = ζ ^ d := by sorry
