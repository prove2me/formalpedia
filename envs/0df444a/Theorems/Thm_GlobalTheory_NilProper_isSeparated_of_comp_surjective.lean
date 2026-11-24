-- Prove2me | Theorems.Thm_GlobalTheory_NilProper_isSeparated_of_comp_surjective
-- name    : GlobalTheory.NilProper.isSeparated_of_comp_surjective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:43:09.57717+00:00
-- url     : https://prove2.me/theorems/881eb4ac-e6b0-40a7-a5ca-b8713c573ac8
-- title:
--   Nil Proper: is Separated of comp surjective
-- statement:
--   The Nil Proper construction uses the is Separated of comp surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsProperAndGeometricallyConnectedOfIsNilpotent.lean#L14-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsProperAndGeometricallyConnectedOfIsNilpotent.lean#L14-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsProperAndGeometricallyConnectedOfIsNilpotent
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
open GlobalTheory GlobalTheory.NilProper

theorem GlobalTheory.NilProper.isSeparated_of_comp_surjective {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [UniversallyClosed j] [IsSeparated (j ≫ f)] : IsSeparated f := by sorry
