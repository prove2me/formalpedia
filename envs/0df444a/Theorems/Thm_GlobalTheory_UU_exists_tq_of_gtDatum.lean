-- Prove2me | Theorems.Thm_GlobalTheory_UU_exists_tq_of_gtDatum
-- name    : GlobalTheory.UU.exists_tq_of_gtDatum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T16:02:44.071643+00:00
-- url     : https://prove2.me/theorems/69963ec5-81c8-4eaf-83ec-3c7c3b747f68
-- title:
--   UU: exists tq of gt Datum
-- statement:
--   The UU construction uses the exists tq of gt Datum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsMemCommonChart.lean#L127-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsMemCommonChart.lean#L127-L130

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMemCommonChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S : Scheme.{0}}
attribute [local instance] SplitExt.free SplitExt.finite
variable {E : SplitExt S} {G : Over S} [GrpObj G]

theorem GlobalTheory.UU.exists_tq_of_gtDatum :
    ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] (Dat : E.GtDatum G), ∃ Q : TQ G E.X, Q.i = Dat.i := by sorry
