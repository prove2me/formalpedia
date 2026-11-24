-- Prove2me | Theorems.Thm_GlobalTheory_K5_Basic_tw_exists_prim_p
-- name    : GlobalTheory.K5.Basic.tw_exists_prim_p
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:42:03.511507+00:00
-- url     : https://prove2.me/theorems/af567b71-5333-4e79-8dde-b36d2ff0c8be
-- title:
--   Basic: tw exists prim p
-- statement:
--   The Basic construction uses the tw exists prim p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L283-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L283-L287

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

theorem GlobalTheory.K5.Basic.tw_exists_prim_p (Ω : Type*) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] :
    ∃ z : Ω, IsPrimitiveRoot z p := by sorry
