-- Prove2me | Theorems.Thm_GlobalTheory_norm_innerFormLeft_le
-- name    : GlobalTheory.norm_innerFormLeft_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:20.810214+00:00
-- url     : https://prove2.me/theorems/94999a86-1a1f-4fec-b686-cfe13f5af8aa
-- title:
--   Global Theory: norm inner Form Left le
-- statement:
--   The Global Theory construction uses the norm inner Form Left le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L312-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L312-L313

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

theorem GlobalTheory.norm_innerFormLeft_le (u v : V) : ‖innerFormLeft V u v‖ ≤ ‖u‖ * ‖v‖ := by sorry
