-- Prove2me | Theorems.Thm_GlobalTheory_regular_of_forall_padic_point_norm_le_one
-- name    : GlobalTheory.regular_of_forall_padic_point_norm_le_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:16:14.223293+00:00
-- url     : https://prove2.me/theorems/dd3819bf-3939-5df5-9a05-68d35c80a0f6
-- title:
--   Global Theory: regular of forall padic point norm le one
-- statement:
--   The Global Theory construction uses the regular of forall padic point norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L460-L490
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L460-L490

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
local notation "genericPt(" p ", " K ", " y ")" =>
  Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y
variable {Z : Scheme.{0}} [IsIntegral Z] (π : Z ⟶ Spec (.of ℤ)) [Flat π] [LocallyOfFiniteType π]
include π
omit π [IsIntegral Z] [Flat π] [LocallyOfFiniteType π]

theorem GlobalTheory.regular_of_forall_padic_point_norm_le_one :
    (∀ (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [IsDomain A] [CharZero A]
      [Algebra.FiniteType ℤ A] (m : Ideal A) [m.IsMaximal], (p : A) ∈ m →
      IsIntegrallyClosed (Localization.AtPrime m) → ∀ a : A, a ≠ 0 → ∀ φ : Localization.Away a,
      (∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
        (y : A →+* integralClosure ℤ_[p] K) (hya : y a ≠ 0),
        (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m →
          ‖(IsLocalization.Away.lift a (isUnit_val_comp_of_ne_zero y hya) φ :
            PadicAlgCl p)‖ ≤ 1) →
      ∃ s ∉ m, ∃ b : A, algebraMap A _ s * φ = algebraMap A _ b) ∧
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (π : Z ⟶ Spec (.of ℤ)) [Flat π] [LocallyOfFiniteType π]
      (U : Z.Opens) [Nonempty U] (φ : Γ(Z, U)),
      (∀ (p : ℕ) [Fact p.Prime] (x : Z), IsClosed ({x} : Set Z) → (p : Z.residueField x) = 0 →
        IsIntegrallyClosed (Z.presheaf.stalk x) →
        (∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
          (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ Z) (hy : ⊤ ≤ (genericPt(p, K, y)) ⁻¹ᵁ U),
          y (closedPoint (integralClosure ℤ_[p] K)) = x →
            ‖(((Scheme.ΓSpecIso (.of K)).hom ((genericPt(p, K, y)).appLE U ⊤ hy φ) : K) :
              PadicAlgCl p)‖ ≤ 1) →
        Z.germToFunctionField U φ ∈ (algebraMap (Z.presheaf.stalk x) Z.functionField).range) ∧
      (IsNormalScheme Z → ∀ (W : Z.Opens) [Nonempty W],
        (∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
          [FiniteDimensional ℚ_[p] K] (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ Z)
          (hy : ⊤ ≤ (genericPt(p, K, y)) ⁻¹ᵁ U), y (closedPoint (integralClosure ℤ_[p] K)) ∈ W →
            ‖(((Scheme.ΓSpecIso (.of K)).hom ((genericPt(p, K, y)).appLE U ⊤ hy φ) : K) :
              PadicAlgCl p)‖ ≤ 1) →
        ∃ ψ : Γ(Z, W), Z.germToFunctionField W ψ = Z.germToFunctionField U φ) := by sorry
