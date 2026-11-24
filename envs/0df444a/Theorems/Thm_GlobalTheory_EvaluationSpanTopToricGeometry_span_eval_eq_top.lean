-- Prove2me | Theorems.Thm_GlobalTheory_EvaluationSpanTopToricGeometry_span_eval_eq_top
-- name    : GlobalTheory.EvaluationSpanTopToricGeometry.span_eval_eq_top
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:06:22.194797+00:00
-- url     : https://prove2.me/theorems/fb0ddcc1-5488-4976-95fe-423e9cc0b47d
-- title:
--   Evaluation Span Top Toric Geometry: span eval eq top
-- statement:
--   The Evaluation Span Top Toric Geometry construction uses the span eval eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/SpanEvalEqTop.lean#L5-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/SpanEvalEqTop.lean#L5-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SpanEvalEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EvaluationSpanTopToricGeometry

theorem GlobalTheory.EvaluationSpanTopToricGeometry.span_eval_eq_top {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V] :
    Submodule.span ℂ (Set.range fun x : X => ((LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype))
      = ⊤ := by sorry
