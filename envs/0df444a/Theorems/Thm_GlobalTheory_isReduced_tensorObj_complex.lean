-- Prove2me | Theorems.Thm_GlobalTheory_isReduced_tensorObj_complex
-- name    : GlobalTheory.isReduced_tensorObj_complex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:30.404815+00:00
-- url     : https://prove2.me/theorems/a8edc1f7-3b1b-4796-afae-f4c6f77b0a13
-- title:
--   Global Theory: is Reduced tensor Obj complex
-- statement:
--   The Global Theory construction uses the is Reduced tensor Obj complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsReducedTensorObjComplex.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsReducedTensorObjComplex.lean#L14-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedTensorObjComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.isReduced_tensorObj_complex :
    (∀ (X Y : Over (Sp ℂ)), IsReduced X.left → IsReduced Y.left → LocallyOfFiniteType X.hom → LocallyOfFiniteType Y.hom → IsReduced (X ⊗ Y).left) := by sorry
