-- Prove2me | Theorems.Thm_GlobalTheory_T_finiteDimensional_span_of_forall_linear_bounded
-- name    : GlobalTheory.T.finiteDimensional_span_of_forall_linear_bounded
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:27.383824+00:00
-- url     : https://prove2.me/theorems/8da0eaa7-d0fa-460d-bfc8-a9ae2fa15586
-- title:
--   T: finite Dimensional span of forall linear bounded
-- statement:
--   The T construction uses the finite Dimensional span of forall linear bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanFiniteDimensionalOfBoundedFormsStatement.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanFiniteDimensionalOfBoundedFormsStatement.lean#L7-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanFiniteDimensionalOfBoundedForms
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanFiniteDimensionalOfBoundedFormsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finiteDimensional_span_of_forall_linear_bounded : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s) := by sorry
