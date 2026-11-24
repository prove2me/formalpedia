-- Prove2me | Theorems.Thm_GlobalTheory_exists_point_over_dominant_geometric_point
-- name    : GlobalTheory.exists_point_over_dominant_geometric_point
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:36:28.101273+00:00
-- url     : https://prove2.me/theorems/09686b98-e2fb-44ed-9ad8-4c9193d13d52
-- title:
--   Global Theory: exists point over dominant geometric point
-- statement:
--   The Global Theory construction uses the exists point over dominant geometric point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqOfDominantGeometricPointsOfUnramified.lean#L17-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqOfDominantGeometricPointsOfUnramified.lean#L17-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqOfDominantGeometricPointsOfUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
universe u
open GlobalTheory

theorem GlobalTheory.exists_point_over_dominant_geometric_point {U S : Scheme.{u}} (g : U ⟶ S)
    [UniversallyOpen g] [LocallyOfFiniteType g] [Nonempty U] {F : Type u} [Field F]
    [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t] :
    ∃ j : Spec (.of F) ⟶ U, j ≫ g = t := by sorry
