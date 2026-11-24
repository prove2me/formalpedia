-- Prove2me | Theorems.Thm_GlobalTheory_LiftTest_gs_comp
-- name    : GlobalTheory.LiftTest.gs_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:40.780723+00:00
-- url     : https://prove2.me/theorems/e49b1bd2-e019-4ba9-97dc-2017f60af317
-- title:
--   Lift Test: gs comp
-- statement:
--   The Lift Test construction uses the gs comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/StalkMapInjectiveOfFlat.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/StalkMapInjectiveOfFlat.lean#L23-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
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
open GlobalTheory GlobalTheory.LiftTest

theorem GlobalTheory.LiftTest.gs_comp {W Z Y : Scheme.{0}} (f : W ⟶ Z) (r : Z ⟶ Y) (w : W) (U : Y.Opens) (h : r (f w) ∈ U)
    (a : Γ(Y, U)) : gs (f ≫ r) w U a = (f.stalkMap w).hom (gs r (f w) U a) := by sorry
