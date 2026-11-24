-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Form_div_nsmul
-- name    : GlobalTheory.Ex.NumD.Form.div_nsmul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:06:10.664689+00:00
-- url     : https://prove2.me/theorems/67c62170-7fdb-40b6-a60a-250ef8003554
-- title:
--   Form: div nsmul
-- statement:
--   The Form construction uses the div nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TwistTerms.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TwistTerms.lean#L23-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)

theorem GlobalTheory.Ex.NumD.Form.div_nsmul {N : NumD O} {k : ℕ} (β : N.Form k) {j : ℕ} (hj : j ∣ k) (m : ℕ) (x y : N.X) :
    β.be x (m • y) / j = β.be x y / j * m := by sorry
