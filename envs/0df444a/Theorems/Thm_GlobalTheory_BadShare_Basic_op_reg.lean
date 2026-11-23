-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_Basic_op_reg
-- name    : GlobalTheory.BadShare.Basic.op_reg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:18.654311+00:00
-- url     : https://prove2.me/theorems/d54c430e-f04b-43e1-b886-32cfa7518fde
-- title:
--   Basic: op reg
-- statement:
--   The Basic construction uses the op reg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L446-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L446-L448

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

theorem GlobalTheory.BadShare.Basic.op_reg (e f : G → ℂ) : op (regFn G) e f = conv e f := by sorry
