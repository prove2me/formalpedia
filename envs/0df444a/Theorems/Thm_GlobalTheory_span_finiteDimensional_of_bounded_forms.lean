-- Prove2me | Theorems.Thm_GlobalTheory_span_finiteDimensional_of_bounded_forms
-- name    : GlobalTheory.span_finiteDimensional_of_bounded_forms
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:21:24.56793+00:00
-- url     : https://prove2.me/theorems/a1cd29d1-533f-493e-a840-31cf18e9e158
-- title:
--   Global Theory: span finite Dimensional of bounded forms
-- statement:
--   The Global Theory construction uses the span finite Dimensional of bounded forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanFiniteDimensionalOfBoundedForms.lean#L7-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanFiniteDimensionalOfBoundedForms.lean#L7-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanFiniteDimensionalOfBoundedForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
open GlobalTheory

theorem GlobalTheory.span_finiteDimensional_of_bounded_forms {V : Type} [AddCommGroup V] [Module ℂ V]
    (s : Set V) (hs : ∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) :
    FiniteDimensional ℂ (Submodule.span ℂ s) := by sorry
