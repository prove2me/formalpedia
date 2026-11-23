-- Prove2me | Theorems.Thm_GlobalTheory_isRegularRing_of_smooth
-- name    : GlobalTheory.isRegularRing_of_smooth
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:03.453728+00:00
-- url     : https://prove2.me/theorems/30a8050c-fb90-4375-b7c7-b29df752a3a8
-- title:
--   Global Theory: is Regular Ring of smooth
-- statement:
--   The Global Theory construction uses the is Regular Ring of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsRegularRingOfSmooth.lean#L47-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsRegularRingOfSmooth.lean#L47-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.isRegularRing_of_smooth :
    ∀ (V B : Type) [CommRing V] [IsRegularRing V] [CommRing B] [Algebra V B] [Algebra.Smooth V B],
      IsRegularRing B := by sorry
