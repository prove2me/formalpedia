-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_Basic_standard_five_nontrivial
-- name    : GlobalTheory.BadShare.Basic.standard_five_nontrivial
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:27.319788+00:00
-- url     : https://prove2.me/theorems/1aa28b1a-779b-5635-aa44-7385adf62b07
-- title:
--   Basic: standard five nontrivial
-- statement:
--   The Basic construction uses the standard five nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L255-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L255-L278

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

theorem GlobalTheory.BadShare.Basic.standard_five_nontrivial :
    (∃ u, (levStandard g 5 true 1 2 (by norm_num)).Mem u ∧ (levStandard g 5 true 1 2 (by norm_num)).chi u ≠ 1) ∧
      ∃ u, IsUp g 5 u ∧ ¬ (levStandard g 5 true 1 2 (by norm_num)).Mem u := by sorry
