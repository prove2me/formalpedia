-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_sval_eq_powVal
-- name    : GlobalTheory.FieldBaseChange.sval_eq_powVal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:24.141097+00:00
-- url     : https://prove2.me/theorems/0d9308cf-0fb3-43b0-a5b1-c5f93f84cf3d
-- title:
--   Field Base Change: sval eq pow Val
-- statement:
--   The Field Base Change construction uses the sval eq pow Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSecOfLocal.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSecOfLocal.lean#L31-L33

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

theorem GlobalTheory.FieldBaseChange.sval_eq_powVal {L : LB X₁} {g : Z₁ ⟶ X₁} {k : ℤ}
    (a : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k))) (r : Z ⟶ Z₁) (z : Z)
    (J : (Z ⟶ X₁) → L.ι) : sval a r z J = powVal a r z (J (r ≫ g)) := by sorry
