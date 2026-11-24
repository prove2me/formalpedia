-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_Basic_rk_reg
-- name    : GlobalTheory.BadShare.Basic.rk_reg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:59:25.052576+00:00
-- url     : https://prove2.me/theorems/8a83d036-0ad8-4648-a04b-0e81b47c4e4a
-- title:
--   Basic: rk reg
-- statement:
--   The Basic construction uses the rk reg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L464-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L464-L469

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
variable (G : Type) [Group G] [Fintype G]
variable {G}

theorem GlobalTheory.BadShare.Basic.rk_reg (e : G → ℂ) (he : conv e e = e) : (rk (regFn G) e : ℂ) = Fintype.card G * e 1 := by sorry
