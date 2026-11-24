-- Prove2me | Theorems.Thm_GlobalTheory_TraceFormNondegenerate_span_eq_top_of_trace_eq
-- name    : GlobalTheory.TraceFormNondegenerate.span_eq_top_of_trace_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:59:43.296796+00:00
-- url     : https://prove2.me/theorems/de65804f-9610-49cd-8c92-545fabbebec9
-- title:
--   Trace Form Nondegenerate: span eq top of trace eq
-- statement:
--   The Trace Form Nondegenerate construction uses the span eq top of trace eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanEqTopOfTraceEq.lean#L12-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanEqTopOfTraceEq.lean#L12-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanEqTopOfTraceEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TraceFormNondegenerate

theorem GlobalTheory.TraceFormNondegenerate.span_eq_top_of_trace_eq {Γ K : Type} [Monoid Γ] [Field K] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) K)
    (htr : ∀ g : Γ, Matrix.trace (M g) = Matrix.trace (N g))
    (hN : Submodule.span K (Set.range (⇑N : Γ → Matrix (Fin n) (Fin n) K)) = ⊤) :
    Submodule.span K (Set.range (⇑M : Γ → Matrix (Fin n) (Fin n) K)) = ⊤ := by sorry
