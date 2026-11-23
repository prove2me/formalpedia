-- Prove2me | Theorems.Thm_GlobalTheory_ReducedSubgroup_geometricallyReduced_of_perfectField
-- name    : GlobalTheory.ReducedSubgroup.geometricallyReduced_of_perfectField
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:07.625805+00:00
-- url     : https://prove2.me/theorems/c06ea2b5-8d26-4589-ac2c-d04d3545203b
-- title:
--   Reduced Subgroup: geometrically Reduced of perfect Field
-- statement:
--   The Reduced Subgroup construction uses the geometrically Reduced of perfect Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GeometricallyReducedOfPerfectField.lean#L78-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GeometricallyReducedOfPerfectField.lean#L78-L96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ReducedSubgroup
universe u

theorem GlobalTheory.ReducedSubgroup.geometricallyReduced_of_perfectField {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsReduced X] (f : X ⟶ Spec (.of k)) : GeometricallyReduced f := by sorry
