-- Prove2me | Theorems.Thm_GlobalTheory_ReducedSubgroup_vanishingIdeal_le_ker
-- name    : GlobalTheory.ReducedSubgroup.vanishingIdeal_le_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:52:07.588008+00:00
-- url     : https://prove2.me/theorems/58b603f1-63e8-47a5-8b36-5027d8f5493e
-- title:
--   Reduced Subgroup: vanishing Ideal le ker
-- statement:
--   The Reduced Subgroup construction uses the vanishing Ideal le ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GeometricallyReducedOfPerfectField.lean#L68-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GeometricallyReducedOfPerfectField.lean#L68-L76

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
open Scheme.IdealSheafData

theorem GlobalTheory.ReducedSubgroup.vanishingIdeal_le_ker {T X : Scheme.{u}} [IsReduced T] (g : T ⟶ X)
    (Z : TopologicalSpace.Closeds X) (h : Set.range g ⊆ Z) : vanishingIdeal Z ≤ g.ker := by sorry
