-- Prove2me | Theorems.Thm_GlobalTheory_ReducedSubgroup_isReduced_subscheme_vanishingIdeal
-- name    : GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:30.107895+00:00
-- url     : https://prove2.me/theorems/fe7d5a1a-8699-462c-8181-4e89a385f51e
-- title:
--   Reduced Subgroup: is Reduced subscheme vanishing Ideal
-- statement:
--   The Reduced Subgroup construction uses the is Reduced subscheme vanishing Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GeometricallyReducedOfPerfectField.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GeometricallyReducedOfPerfectField.lean#L58-L64

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

theorem GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme := by sorry
