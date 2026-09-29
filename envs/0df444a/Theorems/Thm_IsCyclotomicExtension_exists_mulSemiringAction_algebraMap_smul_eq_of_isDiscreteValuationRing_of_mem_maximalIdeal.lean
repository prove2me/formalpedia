-- Prove2me | Theorems.Thm_IsCyclotomicExtension_exists_mulSemiringAction_algebraMap_smul_eq_of_isDiscreteValuationRing_of_mem_maximalIdeal
-- name    : IsCyclotomicExtension.exists_mulSemiringAction_algebraMap_smul_eq_of_isDiscreteValuationRing_of_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/cac3dcde-e9a6-5312-8b53-ccc53812ca98
-- title:
--   Galois action on a discrete valuation ring in ℚ(ζₚ)
-- statement:
--   Let $p$ be a prime and let $L$ be a field of characteristic zero that is a $p$-th cyclotomic extension of $\mathbb{Q}$, together with an element $\zeta \in L$ which is a primitive $p$-th root of unity. Let $A$ be a commutative domain which is a discrete valuation ring, equipped with an algebra structure over which $L$ is its fraction field (so the structure map $A \to L$ identifies $L$ with the field of fractions of $A$). Assume that the image of $p$ in $A$ lies in the maximal ideal of the local ring $A$, and that $\zeta$ lies in the image of the structure map, i.e. there is $z \in A$ with $z \mapsto \zeta$. Then there exists an action of the group $L \simeq_{\mathbb{Q}} L$ of $\mathbb{Q}$-algebra automorphisms of $L$ on $A$ by ring automorphisms (a `MulSemiringAction`) such that the structure map $A \to L$ is equivariant: for every automorphism $s$ of $L$ over $\mathbb{Q}$ and every $a \in A$, the image of $s \cdot a$ in $L$ equals $s$ applied to the image of $a$.
--
--   This records that a discrete valuation ring with fraction field $\mathbb{Q}(\zeta_p)$ in which $p$ is not a unit is stable under the Galois group, $p$ being totally ramified so that there is a single place above it; the resulting action restricts the Galois action on $L$. It supplies the Galois-equivariant integral model used downstream in the analysis of $q$-expansions on the modular curve, where an abstract such $A$ together with its Galois action is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsCyclotomicExtension_exists_mulSemiringAction_algebraMap_smul_eq_of_isDiscreteValuationRing_of_mem_maximalIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsCyclotomicExtension.exists_mulSemiringAction_algebraMap_smul_eq_of_isDiscreteValuationRing_of_mem_maximalIdeal
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ) :
    ∃ inst : MulSemiringAction (L ≃ₐ[ℚ] L) A,
      ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a) := by sorry
