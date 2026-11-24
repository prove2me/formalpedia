-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_exists_splits_top
-- name    : GlobalTheory.KuennethOne.exists_splits_top
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:57:38.244974+00:00
-- url     : https://prove2.me/theorems/275444ab-dc97-4843-9509-cbca9b37fd6b
-- title:
--   Kuenneth One: exists splits top
-- statement:
--   The Kuenneth One construction uses the exists splits top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenInfOfIsSeparated.lean#L154-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenInfOfIsSeparated.lean#L154-L196

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenInfOfIsSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.KuennethOne
open TopologicalSpace TensorProduct
variable {S X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {iX : X ⟶ S} {iY : Y ⟶ S}
  (H : IsPullback p q iX iY) {I : Type} {V : I → Z.Opens} {φ : ∀ a b, Γ(Z, V a ⊓ V b)}
include H

theorem GlobalTheory.KuennethOne.exists_splits_top [IsAffine S] [Flat iY] [CompactSpace X] [QuasiSeparatedSpace X]
    (hY : ∀ U U' : Y.Opens, IsAffineOpen U → IsAffineOpen U' → IsAffineOpen (U ⊓ U'))
    (hiX : Function.Bijective iX.appTop.hom) {t : Y ⟶ Z} (ht : t ≫ q = 𝟙 Y)
    (hV : ⨆ a, V a = ⊤) (ρ : ∀ a, Γ(Y, t ⁻¹ᵁ V a))
    (hρ : ∀ a b, (t.app (V a ⊓ V b)).hom (φ a b) =
      rs (t.preimage_mono inf_le_left) (ρ a) - rs (t.preimage_mono inf_le_right) (ρ b))
    (hτ : ∀ W : Y.affineOpens, ∃ τ, Splits V φ (q ⁻¹ᵁ W.1) τ) : ∃ χ, Splits V φ ⊤ χ := by sorry
