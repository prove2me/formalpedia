-- Prove2me | Theorems.Thm_GlobalTheory_EquivDesc_act_comp
-- name    : GlobalTheory.EquivDesc.act_comp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:36:08.123166+00:00
-- url     : https://prove2.me/theorems/860c9282-9edc-4df2-a5d4-64920f7134be
-- title:
--   Equiv Desc: act comp
-- statement:
--   The Equiv Desc construction uses the act comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean#L173-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean#L173-L179

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
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
open GlobalTheory.UU TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.EquivDesc
variable {S : Scheme.{0}}
variable {G B H : Over S} [GrpObj G] [GrpObj B] [GrpObj H] {q : G ⟶ B} {i : H ⟶ G} [IsMonHom q] [IsMonHom i]
  {L : LB G.left} {a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])}
omit [GrpObj H] [IsMonHom i]

theorem GlobalTheory.EquivDesc.act_comp (hk : IsPullback i (toUnit _) q η[B]) {T : Over S} (t : T ⟶ H) (x : T ⟶ G) :
    ((t ≫ i) * x).left ≫ q.left = x.left ≫ q.left := by sorry
