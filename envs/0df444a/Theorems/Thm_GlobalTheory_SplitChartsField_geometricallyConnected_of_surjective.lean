-- Prove2me | Theorems.Thm_GlobalTheory_SplitChartsField_geometricallyConnected_of_surjective
-- name    : GlobalTheory.SplitChartsField.geometricallyConnected_of_surjective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T17:48:05.003161+00:00
-- url     : https://prove2.me/theorems/b3f95142-4274-48f6-8d1f-a21359966eed
-- title:
--   Split Charts Field: geometrically Connected of surjective
-- statement:
--   The Split Charts Field construction uses the geometrically Connected of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitChartsTorusExtensionOverField.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitChartsTorusExtensionOverField.lean#L19-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemRangeAppLEChartIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeightZeroSumOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGroupQuotientPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorusQuotientSchemeOverNilpotentThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitChartsTorusExtensionOverField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.SplitChartsField
open GlobalTheory.UU GlobalTheory.AffineThickening GlobalTheory.TorusQuotientLift GlobalTheory.LocalWeightUnits

theorem GlobalTheory.SplitChartsField.geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by sorry
