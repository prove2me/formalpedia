-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_isoVal_trans
-- name    : GlobalTheory.FieldBaseChange.isoVal_trans
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:16:29.147803+00:00
-- url     : https://prove2.me/theorems/3da0f183-3d1a-4cce-b63c-c6a91a50a662
-- title:
--   Field Base Change: iso Val trans
-- statement:
--   The Field Base Change construction uses the iso Val trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSecOfLocal.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSecOfLocal.lean#L19-L25

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

theorem GlobalTheory.FieldBaseChange.isoVal_trans {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} (hw : w.IsGen) (r : Z ⟶ Y) (z : Z)
    {i₂ j₂ : L₂.ι} {i₁ j₁ : L₁.ι} (a₂ : f₂ (r z) ∈ L₂.U i₂) (b₂ : f₂ (r z) ∈ L₂.U j₂)
    (a₁ : f₁ (r z) ∈ L₁.U i₁) (b₁ : f₁ (r z) ∈ L₁.U j₁) :
    isoVal w r z i₂ i₁ = gm (r ≫ f₂) z _ (L₂.g i₂ j₂) * (gm (r ≫ f₁) z _ (L₁.g i₁ j₁))⁻¹ * isoVal w r z j₂ j₁ := by sorry
