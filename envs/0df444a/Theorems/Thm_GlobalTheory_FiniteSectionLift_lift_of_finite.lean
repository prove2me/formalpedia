-- Prove2me | Theorems.Thm_GlobalTheory_FiniteSectionLift_lift_of_finite
-- name    : GlobalTheory.FiniteSectionLift.lift_of_finite
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:04:52.729827+00:00
-- url     : https://prove2.me/theorems/aaeddd09-4fb5-521d-86f1-167e011587f3
-- title:
--   Finite Section Lift: lift of finite
-- statement:
--   The Finite Section Lift construction uses the lift of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSectionOfFinite.lean#L34-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSectionOfFinite.lean#L34-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSectionOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.FiniteSectionLift

theorem GlobalTheory.FiniteSectionLift.lift_of_finite : ∀ (R K : CommRingCat) (φ : R ⟶ K),
    Function.Injective (⇑(CommRingCat.Hom.hom φ) : (↑R : Type) → (↑K : Type)) →
    (∀ (x : (↑K : Type)), RingHom.IsIntegralElem (CommRingCat.Hom.hom φ) x →
      ∃ (r : (↑R : Type)), (CommRingCat.Hom.hom φ : (↑R : Type) → (↑K : Type)) r = x) →
    ∀ (Z P : AlgebraicGeometry.Scheme) (p : Z ⟶ P) (ξ₀ : AlgebraicGeometry.Spec R ⟶ P)
      (y : AlgebraicGeometry.Spec K ⟶ Z), AlgebraicGeometry.IsFinite p →
      CategoryTheory.CategoryStruct.comp y p =
        CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map φ) ξ₀ →
      ∃ (ξ : AlgebraicGeometry.Spec R ⟶ Z),
        CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map φ) ξ = y ∧
        CategoryTheory.CategoryStruct.comp ξ p = ξ₀ := by sorry
