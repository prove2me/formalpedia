-- Prove2me | Theorems.Thm_GlobalTheory_EvaluationSpanTop_span_eval_eq_top
-- name    : GlobalTheory.EvaluationSpanTop.span_eval_eq_top
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:06:08.052445+00:00
-- url     : https://prove2.me/theorems/da3175ff-45aa-4983-ae10-4fd42b6f331a
-- title:
--   Evaluation Span Top: span eval eq top
-- statement:
--   The Evaluation Span Top construction uses the span eval eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanEvalEqTop.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanEvalEqTop.lean#L7-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanEvalEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EvaluationSpanTop
open Module

theorem GlobalTheory.EvaluationSpanTop.span_eval_eq_top {κ : Type} (W : Submodule ℂ (κ → ℂ)) [FiniteDimensional ℂ W] :
    Submodule.span ℂ (Set.range fun k : κ => (LinearMap.proj k : (κ → ℂ) →ₗ[ℂ] ℂ).comp W.subtype) = ⊤ := by sorry
