-- Prove2me | Theorems.Thm_GlobalTheory_Cartier_SecMaps_ratSecs_eq
-- name    : GlobalTheory.Cartier.SecMaps.ratSecs_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:02.161653+00:00
-- url     : https://prove2.me/theorems/da9f8f6c-80d2-47d3-89d8-37517316b99c
-- title:
--   Sec Maps: rat Secs eq
-- statement:
--   The Sec Maps construction uses the rat Secs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L459-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L459-L482

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

theorem GlobalTheory.Cartier.SecMaps.ratSecs_eq {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} {a : A.Sec}
    {b : B.Sec} (hw : SecMaps w a b) (V : X.Opens) [Nonempty V] : ratSecs a V = ratSecs b V := by sorry
