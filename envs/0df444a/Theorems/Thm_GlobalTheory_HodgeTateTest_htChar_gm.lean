-- Prove2me | Theorems.Thm_GlobalTheory_HodgeTateTest_htChar_gm
-- name    : GlobalTheory.HodgeTateTest.htChar_gm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:09:23.630485+00:00
-- url     : https://prove2.me/theorems/f6a5f460-3083-5da5-be34-57cccf0d4cce
-- title:
--   Hodge Tate Test: ht Char gm
-- statement:
--   The Hodge Tate Test construction uses the ht Char gm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/HtCharOfIsUnit.lean#L106-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/HtCharOfIsUnit.lean#L106-L114

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

theorem GlobalTheory.HodgeTateTest.htChar_gm (p : ℕ) {C : Type} [Field C] (v : Valuation C NNReal) [Algebra O C]
    [Nontrivial O] : HTChar p v (GmO O) ∧ omega (GmO O) ≠ ⊥ := by sorry
