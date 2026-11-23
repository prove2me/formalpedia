-- Prove2me | Theorems.Thm_GlobalTheory_innerFormLeft_apply
-- name    : GlobalTheory.innerFormLeft_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:39.127803+00:00
-- url     : https://prove2.me/theorems/575a58fa-25ec-433a-af3f-9187a5145874
-- title:
--   Global Theory: inner Form Left apply
-- statement:
--   The Global Theory construction uses the inner Form Left apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L310-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L310-L310

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem GlobalTheory.innerFormLeft_apply (u v : V) : innerFormLeft V u v = inner ℂ v u := by sorry

attribute [defeq] GlobalTheory.innerFormLeft_apply
