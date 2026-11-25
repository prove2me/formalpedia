-- Prove2me | Theorems.Thm_GlobalTheory_IsoDesc_IsQuot_trans
-- name    : GlobalTheory.IsoDesc.IsQuot.trans
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:10:09.71278+00:00
-- url     : https://prove2.me/theorems/a68d4c07-14c7-41ee-b771-9403df41d6c8
-- title:
--   Is Quot: trans
-- statement:
--   The Is Quot construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsCPMapDescends.lean#L115-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsCPMapDescends.lean#L115-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.IsoDesc
variable {X Y Z : Scheme.{0}}
variable {G B' B : Scheme.{0}} {L : LB G} {M' : LB B'} {M : LB B} {q : G ⟶ B'} {β : B' ⟶ B}

theorem GlobalTheory.IsoDesc.IsQuot.trans (hL : L.IsLB) {u : LB.Iso L (M'.pull q)}
    {w : LB.Iso L (M.pull (q ≫ β))} (hu : PGen u) (hw : PGen w) {s} (hs : IsQuot u w s)
    (f : Y ⟶ G) (y : Y) (j j' : M.ι) (i i' : M'.ι) (hj : β (q (f y)) ∈ M.U j) (hj' : β (q (f y)) ∈ M.U j')
    (hi : q (f y) ∈ M'.U i) (hi' : q (f y) ∈ M'.U i') :
    gm f y _ (s j i) = gm ((f ≫ q) ≫ β) y _ (M.g j j') * (gm (f ≫ q) y _ (M'.g i i'))⁻¹ * gm f y _ (s j' i') := by sorry
