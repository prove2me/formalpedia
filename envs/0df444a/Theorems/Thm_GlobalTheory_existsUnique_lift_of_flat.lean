-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_lift_of_flat
-- name    : GlobalTheory.existsUnique_lift_of_flat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:58.118795+00:00
-- url     : https://prove2.me/theorems/0ed018c1-7a32-474f-b7a4-bf761a6c1282
-- title:
--   Global Theory: exists Unique lift of flat
-- statement:
--   The Global Theory construction uses the exists Unique lift of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLiftOfSchemeTheoreticallyDominant.lean#L59-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLiftOfSchemeTheoreticallyDominant.lean#L59-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
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
open GlobalTheory
variable {S S' : Scheme.{0}} (f : S' ⟶ S) [IsSchemeTheoreticallyDominant f] [QuasiCompact f]

theorem GlobalTheory.existsUnique_lift_of_flat {Y X Z : Over S} (i : Z ⟶ X) (a : Y ⟶ X)
    (a' : (Over.pullback f).obj Y ⟶ (Over.pullback f).obj Z) [Flat Y.hom]
    [IsClosedImmersion i.left] (h : a' ≫ (Over.pullback f).map i = (Over.pullback f).map a) :
    ∃! b : Y ⟶ Z, b ≫ i = a ∧ (Over.pullback f).map b = a' := by sorry
