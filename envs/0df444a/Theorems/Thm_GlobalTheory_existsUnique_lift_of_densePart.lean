-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_lift_of_densePart
-- name    : GlobalTheory.existsUnique_lift_of_densePart
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:43:46.941887+00:00
-- url     : https://prove2.me/theorems/63fc5eff-f865-42fc-996a-236f80205d86
-- title:
--   Global Theory: exists Unique lift of dense Part
-- statement:
--   The Global Theory construction uses the exists Unique lift of dense Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueLiftOfDensePart.lean#L33-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueLiftOfDensePart.lean#L33-L59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLiftOfDensePart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory

theorem GlobalTheory.existsUnique_lift_of_densePart : ∀ (T U X Y : Scheme.{0}) [IsLocallyNoetherian T] (j : U ⟶ T), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (q : Y ⟶ X) (f : T ⟶ X) (g : U ⟶ Y), IsIntegralHom q → g ≫ q = j ≫ f → ∃! h : T ⟶ Y, j ≫ h = g ∧ h ≫ q = f := by sorry
