-- Prove2me | Theorems.Thm_GlobalTheory_K5_Basic_not_isUnit_p
-- name    : GlobalTheory.K5.Basic.not_isUnit_p
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:41:49.205985+00:00
-- url     : https://prove2.me/theorems/4435e6bb-a497-4591-991c-39d67a2dadb5
-- title:
--   Basic: not is Unit p
-- statement:
--   The Basic construction uses the not is Unit p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L219-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L219-L227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial
variable (p : ℕ) [hp : Fact p.Prime]

theorem GlobalTheory.K5.Basic.not_isUnit_p : ¬ IsUnit (p : O0 p) := by sorry
