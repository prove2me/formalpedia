-- Prove2me | Theorems.Thm_GlobalTheory_isPullback_closureMap_of_flat
-- name    : GlobalTheory.isPullback_closureMap_of_flat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:12.236215+00:00
-- url     : https://prove2.me/theorems/63f72cab-e971-497f-b813-48c9655beb16
-- title:
--   Global Theory: is Pullback closure Map of flat
-- statement:
--   The Global Theory construction uses the is Pullback closure Map of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L306-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L306-L309

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

theorem GlobalTheory.isPullback_closureMap_of_flat {W' P' : Scheme.{u}} {j' : W' ⟶ P'} {w : W' ⟶ W}
    {g : P' ⟶ P} (H : IsPullback j' w g j) [Flat g] [QuasiCompact j] :
    IsPullback j'.imageι (closureMap j' j w g H.w) g j.imageι := by sorry
