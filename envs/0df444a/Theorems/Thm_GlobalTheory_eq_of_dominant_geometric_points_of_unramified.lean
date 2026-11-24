-- Prove2me | Theorems.Thm_GlobalTheory_eq_of_dominant_geometric_points_of_unramified
-- name    : GlobalTheory.eq_of_dominant_geometric_points_of_unramified
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:17:39.222438+00:00
-- url     : https://prove2.me/theorems/c281c500-51e1-400f-8e08-25e9fb1cdf48
-- title:
--   Global Theory: eq of dominant geometric points of unramified
-- statement:
--   The Global Theory construction uses the eq of dominant geometric points of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqOfDominantGeometricPointsOfUnramified.lean#L31-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqOfDominantGeometricPointsOfUnramified.lean#L31-L50

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

theorem GlobalTheory.eq_of_dominant_geometric_points_of_unramified {X S T : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] [IsSeparated f] (g : T ⟶ S)
    [UniversallyOpen g] [LocallyOfFiniteType g] {a b : T ⟶ X} (ha : a ≫ f = g) (hb : b ≫ f = g)
    {F : Type u} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (h : ∀ j : Spec (.of F) ⟶ T, j ≫ g = t → j ≫ a = j ≫ b) : a = b := by sorry
