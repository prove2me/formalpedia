-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_exists_splits_preimage
-- name    : GlobalTheory.KuennethOne.exists_splits_preimage
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:56:50.226974+00:00
-- url     : https://prove2.me/theorems/43e85190-9fc1-4873-a640-63b35f85558e
-- title:
--   Kuenneth One: exists splits preimage
-- statement:
--   The Kuenneth One construction uses the exists splits preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenInfOfIsSeparated.lean#L45-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenInfOfIsSeparated.lean#L45-L152

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

theorem GlobalTheory.KuennethOne.exists_splits_preimage [IsAffine S] (hR : IsField Γ(S, ⊤)) [CompactSpace X]
    (hX : ∀ U U' : X.Opens, IsAffineOpen U → IsAffineOpen U' → IsAffineOpen (U ⊓ U'))
    (hY : ∀ U U' : Y.Opens, IsAffineOpen U → IsAffineOpen U' → IsAffineOpen (U ⊓ U'))
    (hiY : Function.Surjective iY.appTop.hom)
    {y : S ⟶ Y} (hy : y ≫ iY = 𝟙 S) {s : X ⟶ Z} (hs : s ≫ p = 𝟙 X) (hs' : s ≫ q = iX ≫ y)
    (W₀ : Y.affineOpens) (hW₀ : ⊤ ≤ y ⁻¹ᵁ W₀.1)
    (hV : ⨆ a, V a = ⊤) (hφ : IsCocycle V φ) (ρ : ∀ a, Γ(X, s ⁻¹ᵁ V a))
    (hρ : ∀ a b, (s.app (V a ⊓ V b)).hom (φ a b) =
      rs (s.preimage_mono inf_le_left) (ρ a) - rs (s.preimage_mono inf_le_right) (ρ b))
    (W : Y.affineOpens) : ∃ τ, Splits V φ (q ⁻¹ᵁ W.1) τ := by sorry
