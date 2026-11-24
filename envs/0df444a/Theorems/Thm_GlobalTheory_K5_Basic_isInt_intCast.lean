-- Prove2me | Theorems.Thm_GlobalTheory_K5_Basic_isInt_intCast
-- name    : GlobalTheory.K5.Basic.isInt_intCast
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:42:13.880342+00:00
-- url     : https://prove2.me/theorems/ed51071e-a9a0-4b55-9230-d26d929bd36e
-- title:
--   Basic: is Int int Cast
-- statement:
--   The Basic construction uses the is Int int Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L365-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L365-L367

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

theorem GlobalTheory.K5.Basic.isInt_intCast (m : ℤ) : IsInt p (m : Ω) := by sorry
