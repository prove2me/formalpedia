-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_powVal_trans
-- name    : GlobalTheory.FieldBaseChange.powVal_trans
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:17:34.854813+00:00
-- url     : https://prove2.me/theorems/72e6f311-4dd7-425e-9be1-a5f94823eef0
-- title:
--   Field Base Change: pow Val trans
-- statement:
--   The Field Base Change construction uses the pow Val trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSecOfLocal.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSecOfLocal.lean#L35-L40

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

theorem GlobalTheory.FieldBaseChange.powVal_trans {L : LB X₁} {g : Z₁ ⟶ X₁} {k : ℤ}
    (a : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k))) (r : Z ⟶ Z₁) (z : Z) {i j : L.ι}
    (hi : g (r z) ∈ L.U i) (hj : g (r z) ∈ L.U j) :
    powVal a r z i = (gm (r ≫ g) z _ (L.g i j) ^ k).val * powVal a r z j := by sorry
