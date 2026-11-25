-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_Basic_primeOK_example
-- name    : GlobalTheory.BadShare.Basic.primeOK_example
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:50.9649+00:00
-- url     : https://prove2.me/theorems/55ebf967-1195-43fe-ba69-330536f6955c
-- title:
--   Basic: prime OK example
-- statement:
--   The Basic construction uses the prime OK example property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L291-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L291-L292

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

theorem GlobalTheory.BadShare.Basic.primeOK_example : PrimeOK 6529 3 17 ∧ Nat.Prime 6529 := by sorry
