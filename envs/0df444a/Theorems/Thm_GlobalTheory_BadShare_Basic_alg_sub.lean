-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_Basic_alg_sub
-- name    : GlobalTheory.BadShare.Basic.alg_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:59:56.953401+00:00
-- url     : https://prove2.me/theorems/0a646eb1-cb66-44af-bc93-d07cefcdd408
-- title:
--   Basic: alg sub
-- statement:
--   The Basic construction uses the alg sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L370-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L370-L371

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
variable {G : Type} [Group G] [Fintype G]

theorem GlobalTheory.BadShare.Basic.alg_sub (a b : G → ℂ) : alg (a - b) = alg a - alg b := by sorry
