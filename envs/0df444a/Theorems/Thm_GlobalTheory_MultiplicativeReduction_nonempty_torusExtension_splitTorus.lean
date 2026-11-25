-- Prove2me | Theorems.Thm_GlobalTheory_MultiplicativeReduction_nonempty_torusExtension_splitTorus
-- name    : GlobalTheory.MultiplicativeReduction.nonempty_torusExtension_splitTorus
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:17:15.108798+00:00
-- url     : https://prove2.me/theorems/be685373-a778-53dc-b167-7c00d2f09b60
-- title:
--   Multiplicative Reduction: nonempty torus Extension split Torus
-- statement:
--   The Multiplicative Reduction construction uses the nonempty torus Extension split Torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonemptyTorusExtensionSplitTorus.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonemptyTorusExtensionSplitTorus.lean#L56-L59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RangeSubsetOfForallField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LiftMulHomPullbackFst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyTorusExtensionSplitTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.MultiplicativeReduction
open GlobalTheory.WeierstrassCurve

theorem GlobalTheory.MultiplicativeReduction.nonempty_torusExtension_splitTorus (K : Type) [Field K] :
    Nonempty (TorusExtension (splitTorus (Spec (CommRingCat.of K)) ℤ)) := by sorry
