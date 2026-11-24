-- Prove2me | Theorems.Thm_GlobalTheory_K5_Basic_charZero_of_isClo
-- name    : GlobalTheory.K5.Basic.charZero_of_isClo
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:41:15.419804+00:00
-- url     : https://prove2.me/theorems/7d2207e8-34b0-4d2a-a468-8a691af46716
-- title:
--   Basic: char Zero of is Clo
-- statement:
--   The Basic construction uses the char Zero of is Clo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L258-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L258-L259

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
variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

theorem GlobalTheory.K5.Basic.charZero_of_isClo (h : IsClo p Ω) : CharZero Ω := by sorry
