-- Prove2me | Theorems.Thm_GlobalTheory_FixedPoint_defined_over_of_fixed
-- name    : GlobalTheory.FixedPoint.defined_over_of_fixed
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:05.269188+00:00
-- url     : https://prove2.me/theorems/8998534a-d994-4d7a-be2a-204bf6b2dfa4
-- title:
--   Fixed Point: defined over of fixed
-- statement:
--   The Fixed Point construction uses the defined over of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean#L124-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean#L124-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFactorOfIsAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.FixedPoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K₀ K₁ L : Type u} [Field K₀] [Field K₁] [Field L]
  [Algebra K₀ K₁] [Algebra K₁ L] [Algebra K₀ L] [IsScalarTower K₀ K₁ L]

theorem GlobalTheory.FixedPoint.defined_over_of_fixed [CharZero K₀] [IsAlgClosed L] :
    (∀ a : L, (∀ s : L ≃ₐ[K₀] L, s a = a) → a ∈ Set.range (algebraMap K₀ L)) ∧
    ∀ (Z : Scheme.{u}) (x : Spec (.of K₁) ⟶ Z),
      (∀ s : L ≃ₐ[K₀] L,
        Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ specAlg(K₁, L) ≫ x = specAlg(K₁, L) ≫ x) →
      (∃! y : Spec (.of K₀) ⟶ Z, specAlg(K₀, K₁) ≫ y = x) ∧
      ∀ (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(Z, U)),
        ((Scheme.ΓSpecIso (.of K₁)).hom (x.appLE U ⊤ h f) : K₁) ∈
          Set.range (algebraMap K₀ K₁) := by sorry
