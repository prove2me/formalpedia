-- Prove2me | Theorems.Thm_GlobalTheory_UU_TQ_locTriv_conclusion
-- name    : GlobalTheory.UU.TQ.locTriv_conclusion
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:19:27.521149+00:00
-- url     : https://prove2.me/theorems/5131bb4a-230c-4224-8b1c-fb183a67fcb0
-- title:
--   TQ: loc Triv conclusion
-- statement:
--   The TQ construction uses the loc Triv conclusion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/LocalTrivialization/LocTrivOfRetraction.lean#L203-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/LocalTrivialization/LocTrivOfRetraction.lean#L203-L214

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
import Definitions.Def_Development_AbelianVarietyTheory_Statements_LocalTrivialization_LocTrivOfRetraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem GlobalTheory.UU.TQ.locTriv_conclusion {G : Over S} [GrpObj G] (Q : TQ G X) :
    Mono Q.i ∧ Flat Q.q.left ∧ Surjective Q.q.left ∧ (Smooth G.hom → Smooth Q.B.hom) ∧
      ∀ (Z : Over S) (g g' : Z ⟶ G), g ≫ Q.q = g' ≫ Q.q ↔ ∃ t : Z ⟶ splitTorus S X, g' = (t ≫ Q.i) * g := by sorry
