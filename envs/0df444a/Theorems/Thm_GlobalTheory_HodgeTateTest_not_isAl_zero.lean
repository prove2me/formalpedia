-- Prove2me | Theorems.Thm_GlobalTheory_HodgeTateTest_not_isAl_zero
-- name    : GlobalTheory.HodgeTateTest.not_isAl_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:06.923174+00:00
-- url     : https://prove2.me/theorems/844e0d51-27c7-53c1-9203-c21e258b65f3
-- title:
--   Hodge Tate Test: not is Al zero
-- statement:
--   The Hodge Tate Test construction uses the not is Al zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/HtCharOfIsUnit.lean#L116-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/HtCharOfIsUnit.lean#L116-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_HtCharOfIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.HodgeTateTest
open GlobalTheory.TangentPow GlobalTheory.GmPoints GlobalTheory.HodgeTateImage
variable {O : Type} [CommRing O]

theorem GlobalTheory.HodgeTateTest.not_isAl_zero (p : ℕ) (hp : ¬IsUnit (p : O)) : ¬IsAl (taut (O := O) p) 0 := by sorry
