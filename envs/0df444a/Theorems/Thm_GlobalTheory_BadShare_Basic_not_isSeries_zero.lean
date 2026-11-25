-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_Basic_not_isSeries_zero
-- name    : GlobalTheory.BadShare.Basic.not_isSeries_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:42.178203+00:00
-- url     : https://prove2.me/theorems/58b0774b-afb3-4dc6-a9a5-aba07ffd3b45
-- title:
--   Basic: not is Series zero
-- statement:
--   The Basic construction uses the not is Series zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L508-L511
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L508-L511

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime] (N : ℕ)
variable {g N}
open GlobalTheory.BadShare.Basic

theorem GlobalTheory.BadShare.Basic.not_isSeries_zero (τ : (ZMod g)[X] → GG g 0 → ℂ) : ¬ IsSeries τ := by sorry
