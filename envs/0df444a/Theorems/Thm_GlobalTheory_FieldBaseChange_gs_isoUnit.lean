-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_gs_isoUnit
-- name    : GlobalTheory.FieldBaseChange.gs_isoUnit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:43.209798+00:00
-- url     : https://prove2.me/theorems/8cb426ce-c3c3-425e-8ca5-710f94f7b91b
-- title:
--   Field Base Change: gs iso Unit
-- statement:
--   The Field Base Change construction uses the gs iso Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSecOfLocal.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSecOfLocal.lean#L81-L86

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

theorem GlobalTheory.FieldBaseChange.gs_isoUnit (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (m : Y' ⟶ Y) (n : ℤ) (i₂ : L₂.ι) (i₁ : L₁.ι)
    {O : Y'.Opens} (hO : O ≤ m ⁻¹ᵁ ((L₂.pull f₂).U (fun _ => i₂) ⊓ (L₁.pull f₁).U (fun _ => i₁)))
    (r : Z ⟶ Y') (z : Z) (hz : r z ∈ O) :
    gs r z O (res hO (pullU m _ (w.s (fun _ => i₂, fun _ => i₁))) ^ n).val = (isoVal w (r ≫ m) z i₂ i₁ ^ n).val := by sorry
