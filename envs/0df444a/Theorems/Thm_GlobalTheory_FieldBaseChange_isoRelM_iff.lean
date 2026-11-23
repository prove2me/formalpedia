-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_isoRelM_iff
-- name    : GlobalTheory.FieldBaseChange.isoRelM_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:16:09.96524+00:00
-- url     : https://prove2.me/theorems/ea3b250f-a8d2-4919-8646-b0df72ab903b
-- title:
--   Field Base Change: iso Rel M iff
-- statement:
--   The Field Base Change construction uses the iso Rel M iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSecOfLocal.lean#L161-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSecOfLocal.lean#L161-L202

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {Y Y' X₁ X₂ Z₁ Z₂ Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}

theorem GlobalTheory.FieldBaseChange.isoRelM_iff (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (m : Y' ⟶ Y) (k : ℕ) {g₁ : Z₁ ⟶ X₁} (h₁ : Y' ⟶ Z₁)
    (e₁ : h₁ ≫ g₁ = m ≫ f₁) {g₂ : Z₂ ⟶ X₂} (h₂ : Y' ⟶ Z₂) (e₂ : h₂ ≫ g₂ = m ≫ f₂)
    (a : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ))))
    (b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ)))) :
    (GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a g₂ h₂ b →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) i₂ i₁, f₂ (m (r z)) ∈ L₂.U i₂ → f₁ (m (r z)) ∈ L₁.U i₁ →
        powVal b (r ≫ h₂) z i₂ = (isoVal w (r ≫ m) z i₂ i₁ ^ (k : ℤ)).val * powVal a (r ≫ h₁) z i₁) ∧
    ((∀ (y : Y') i₂ i₁, f₂ (m y) ∈ L₂.U i₂ → f₁ (m y) ∈ L₁.U i₁ →
        powVal b (𝟙 Y' ≫ h₂) y i₂ = (isoVal w (𝟙 Y' ≫ m) y i₂ i₁ ^ (k : ℤ)).val * powVal a (𝟙 Y' ≫ h₁) y i₁) →
      GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a g₂ h₂ b) := by sorry
