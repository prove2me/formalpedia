-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_kuenneth_injective
-- name    : GlobalTheory.KuennethOne.kuenneth_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:59.227553+00:00
-- url     : https://prove2.me/theorems/4c927970-8809-4238-9fea-eea843e01adb
-- title:
--   Kuenneth One: kuenneth injective
-- statement:
--   The Kuenneth One construction uses the kuenneth injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenInfOfIsSeparated.lean#L206-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenInfOfIsSeparated.lean#L206-L243

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

theorem GlobalTheory.KuennethOne.kuenneth_injective :
    ∀ (K : Type) [Field K] (X Y : Over (Spec (CommRingCat.of K))) (x₀ : 𝟙_ _ ⟶ X) (y₀ : 𝟙_ _ ⟶ Y), IsSeparated X.hom → QuasiCompact X.hom → IsSeparated Y.hom → QuasiCompact Y.hom → Function.Bijective X.hom.appTop.hom → Function.Bijective Y.hom.appTop.hom → ∀ (I : Type) (V : I → (X ⊗ Y).left.Opens), ⨆ a, V a = ⊤ → ∀ φ : ∀ a b, Γ((X ⊗ Y).left, V a ⊓ V b), (∀ a b d, ((X ⊗ Y).left.presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ⊓ V d ≤ V a ⊓ V b)).op).hom (φ a b) + ((X ⊗ Y).left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V a ⊓ V b ⊓ V d ≤ V b ⊓ V d)).op).hom (φ b d) = ((X ⊗ Y).left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V a ⊓ V b ⊓ V d ≤ V a ⊓ V d)).op).hom (φ a d)) → (∃ ψ : ∀ a, Γ(X.left, (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V a), ∀ a b, ((lift (𝟙 X) (toUnit X ≫ y₀)).left.app (V a ⊓ V b)).hom (φ a b) = (X.left.presheaf.map (homOfLE (show (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V a from fun _ h => h.1)).op).hom (ψ a) - (X.left.presheaf.map (homOfLE (show (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V b from fun _ h => h.2)).op).hom (ψ b)) → (∃ ψ : ∀ a, Γ(Y.left, (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V a), ∀ a b, ((lift (toUnit Y ≫ x₀) (𝟙 Y)).left.app (V a ⊓ V b)).hom (φ a b) = (Y.left.presheaf.map (homOfLE (show (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V a from fun _ h => h.1)).op).hom (ψ a) - (Y.left.presheaf.map (homOfLE (show (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V b from fun _ h => h.2)).op).hom (ψ b)) → ∃ ψ : ∀ a, Γ((X ⊗ Y).left, V a), ∀ a b, φ a b = ((X ⊗ Y).left.presheaf.map (homOfLE inf_le_left).op).hom (ψ a) - ((X ⊗ Y).left.presheaf.map (homOfLE inf_le_right).op).hom (ψ b) := by sorry
