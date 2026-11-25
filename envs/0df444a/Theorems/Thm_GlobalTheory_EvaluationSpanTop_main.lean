-- Prove2me | Theorems.Thm_GlobalTheory_EvaluationSpanTop_main
-- name    : GlobalTheory.EvaluationSpanTop.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:47.625938+00:00
-- url     : https://prove2.me/theorems/eeea9486-e6a9-502c-b1d3-635fd24d0566
-- title:
--   Evaluation Span Top: main
-- statement:
--   The Evaluation Span Top construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanEvalEqTop.lean#L22-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanEvalEqTop.lean#L22-L44

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

theorem GlobalTheory.EvaluationSpanTop.main : ∀ {κ : Type} (W : Submodule ℂ (κ → ℂ)) [FiniteDimensional ℂ ↥W], ∃ (m : ℕ) (b : Fin m → κ → ℂ) (c : Fin m → κ →₀ ℂ), (∀ (i : Fin m), b i ∈ W) ∧ ∀ v ∈ W, ∀ (k' : κ), v k' = ∑ i : Fin m, (Finsupp.sum (c i) fun (k : κ) (α : ℂ) ↦ α * v k) * b i k' := by sorry
