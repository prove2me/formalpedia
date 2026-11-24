-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_Basic_standard_edge_five
-- name    : GlobalTheory.BadShare.Basic.standard_edge_five
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:59:33.995002+00:00
-- url     : https://prove2.me/theorems/98a19993-d390-449e-9990-8abcad332f5e
-- title:
--   Basic: standard edge five
-- statement:
--   The Basic construction uses the standard edge five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L232-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L232-L235

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

theorem GlobalTheory.BadShare.Basic.standard_edge_five (a b : Fin 5) : (levStandard g 5 true 1 2 (by norm_num)).Edge a b ↔
    (a, b) = (0, 3) ∨ (a, b) = (1, 2) ∨ (a, b) = (3, 4) := by sorry
