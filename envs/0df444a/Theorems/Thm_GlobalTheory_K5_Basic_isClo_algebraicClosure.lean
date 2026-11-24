-- Prove2me | Theorems.Thm_GlobalTheory_K5_Basic_isClo_algebraicClosure
-- name    : GlobalTheory.K5.Basic.isClo_algebraicClosure
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:42:04.145027+00:00
-- url     : https://prove2.me/theorems/0b378a4f-1616-4641-851a-859b63a9cb62
-- title:
--   Basic: is Clo algebraic Closure
-- statement:
--   The Basic construction uses the is Clo algebraic Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L233-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L233-L239

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

theorem GlobalTheory.K5.Basic.isClo_algebraicClosure : IsClo p (AlgebraicClosure (FractionRing (O0 p))) := by sorry
