-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_closureLift_of_isReduced
-- name    : GlobalTheory.existsUnique_closureLift_of_isReduced
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:44:28.537801+00:00
-- url     : https://prove2.me/theorems/4d615784-f525-461a-a527-91ac7a529006
-- title:
--   Global Theory: exists Unique closure Lift of is Reduced
-- statement:
--   The Global Theory construction uses the exists Unique closure Lift of is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L170-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L170-L174

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
noncomputable section
variable {W P T' T Z : Scheme.{u}} (j : W ⟶ P)

theorem GlobalTheory.existsUnique_closureLift_of_isReduced (t : T ⟶ P) (d : T' ⟶ T) [IsReduced T]
    [IsDominant d] (w : T' ⟶ W) (h : d ≫ t = w ≫ j) :
    ∃! l : T ⟶ j.image, l ≫ j.imageι = t := by sorry
