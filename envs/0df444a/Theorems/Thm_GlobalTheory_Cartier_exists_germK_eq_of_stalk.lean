-- Prove2me | Theorems.Thm_GlobalTheory_Cartier_exists_germK_eq_of_stalk
-- name    : GlobalTheory.Cartier.exists_germK_eq_of_stalk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:20.200369+00:00
-- url     : https://prove2.me/theorems/9b52e7ed-6037-4ef1-af7c-18ebcc50400e
-- title:
--   Cartier: exists germ K eq of stalk
-- statement:
--   The Cartier construction uses the exists germ K eq of stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L399-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L399-L420

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
variable [IsIntegral X]

theorem GlobalTheory.Cartier.exists_germK_eq_of_stalk (U : X.Opens) [Nonempty U] (t : X.functionField)
    (h : ∀ x ∈ U, t ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField)) :
    ∃ a : Γ(X, U), (X.germToFunctionField U).hom a = t := by sorry
