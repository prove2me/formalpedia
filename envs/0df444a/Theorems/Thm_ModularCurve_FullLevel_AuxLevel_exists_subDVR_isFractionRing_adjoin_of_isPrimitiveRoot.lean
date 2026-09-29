-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_subDVR_isFractionRing_adjoin_of_isPrimitiveRoot
-- name    : ModularCurve.FullLevel.AuxLevel.exists_subDVR_isFractionRing_adjoin_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/edd7742f-8bcc-57a2-8036-39f1c989965c
-- title:
--   A cyclotomic sub-DVR with residue degree data and ξ integral
-- statement:
--   Let $q$ and $\ell$ be primes with $\ell \neq q$, let $L$ be a field of characteristic $0$, and let $\xi \in L$ be a primitive $(q\ell)$-th root of unity. Let $A$ be a discrete valuation ring which is a domain, equipped with an algebra structure over which $L$ is its fraction field, and assume $q$ lies in the maximal ideal of $A$. The assertion is the existence of a type $A'$, together with the structure of a commutative ring, a domain and a discrete valuation ring, algebra structures of $A'$ on $A$, on $L$ and on the intermediate field $\mathbb{Q}(\xi) =$ `IntermediateField.adjoin ℚ {ξ}` of $L$, compatibility of these in the towers $A' \to A \to L$ and $A' \to \mathbb{Q}(\xi) \to L$, and the property that $\mathbb{Q}(\xi)$ is the fraction field of $A'$, such that: the structure map $A' \to A$ is injective; the preimage of the maximal ideal of $A$ under it is the maximal ideal of $A'$; $q$ lies in the maximal ideal of $A'$; the residue field of $A'$ is finite; there are $\varpi, \varepsilon \in A'$ with maximal ideal of $A'$ equal to $(\varpi)$, with $\varepsilon$ a unit and $\varpi^{q-1} = \varepsilon q$; and $\xi$ lies in the image of $A' \to L$.
--
--   The intended $A'$ is $A \cap \mathbb{Q}(\xi)$, the valuation ring of the restriction of the valuation of $A$ to the cyclotomic subfield $\mathbb{Q}(\zeta_{q\ell}) \subseteq L$; the final two clauses record that its absolute ramification index at $q$ is exactly $q-1 = \varphi(q)$ (the prime $\ell \neq q$ contributing no ramification) and that the root of unity is integral. The package is stated existentially because its users need only some such discrete valuation ring of arithmetic constants: it is invoked in the reducedness statements for residue field base changes of the level-$\Gamma_0$ and Diamond-type moduli packages at minimal primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_subDVR_isFractionRing_adjoin_of_isPrimitiveRoot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.FullLevel.AuxLevel.exists_subDVR_isFractionRing_adjoin_of_isPrimitiveRoot
    (q : ℕ) [Fact q.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) :
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A')
      (_ : Algebra A' A) (_ : Algebra A' L) (_ : IsScalarTower A' A L)
      (_ : Algebra A' ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)))
      (_ : IsScalarTower A' ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)) L)
      (_ : IsFractionRing A' ↥(IntermediateField.adjoin ℚ ({ξ} : Set L))),
      Function.Injective (algebraMap A' A) ∧
      (IsLocalRing.maximalIdeal A).comap (algebraMap A' A) = IsLocalRing.maximalIdeal A' ∧
      ((q : A') ∈ IsLocalRing.maximalIdeal A') ∧
      Finite (IsLocalRing.ResidueField A') ∧
      (∃ ϖ ε : A', IsLocalRing.maximalIdeal A' = Ideal.span {ϖ} ∧ IsUnit ε ∧ ϖ ^ (q - 1) = ε * (q : A')) ∧
      (∃ r : A', algebraMap A' L r = ξ) := by sorry
