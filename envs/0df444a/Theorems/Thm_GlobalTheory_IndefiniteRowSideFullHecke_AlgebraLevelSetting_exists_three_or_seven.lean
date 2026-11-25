-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_AlgebraLevelSetting_exists_three_or_seven
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.AlgebraLevelSetting.exists_three_or_seven
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:56:49.35174+00:00
-- url     : https://prove2.me/theorems/c0781c19-5763-4321-b031-27bc9493bec5
-- title:
--   Algebra Level Setting: exists three or seven
-- statement:
--   The Algebra Level Setting construction uses the exists three or seven property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/AlgebraLevelSetting.lean#L220-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/AlgebraLevelSetting.lean#L220-L225

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_AlgebraLevelSetting
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AlgebraLevelSetting
attribute [instance] HidaSetting.grp HidaSetting.comm HidaSetting.addX HidaSetting.freeX HidaSetting.finX

theorem GlobalTheory.IndefiniteRowSideFullHecke.AlgebraLevelSetting.exists_three_or_seven (V : Type) [CommRing V] [IsLocalRing V] :
    ∃ n : ℕ, (n = 3 ∨ n = 7) ∧ IsUnit (n : V) := by sorry
