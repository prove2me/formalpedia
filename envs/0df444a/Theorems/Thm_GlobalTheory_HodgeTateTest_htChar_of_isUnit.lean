-- Prove2me | Theorems.Thm_GlobalTheory_HodgeTateTest_htChar_of_isUnit
-- name    : GlobalTheory.HodgeTateTest.htChar_of_isUnit
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:49.4487+00:00
-- url     : https://prove2.me/theorems/7538646e-ff1b-42b2-b0c6-7b8b85bec058
-- title:
--   Hodge Tate Test: ht Char of is Unit
-- statement:
--   The Hodge Tate Test construction uses the ht Char of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/HtCharOfIsUnit.lean#L125-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/HtCharOfIsUnit.lean#L125-L141

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

theorem GlobalTheory.HodgeTateTest.htChar_of_isUnit (p : ℕ) (hp : IsUnit (p : O)) {C : Type} [Field C]
    (v : Valuation C NNReal) [Algebra O C] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] :
    HTChar p v G := by sorry
