-- Prove2me | Theorems.Thm_GlobalTheory_TraceFormNondegenerate_eq_zero_of_trace_mul
-- name    : GlobalTheory.TraceFormNondegenerate.eq_zero_of_trace_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:10:45.254444+00:00
-- url     : https://prove2.me/theorems/71886098-89a1-4632-b518-263b86282285
-- title:
--   Trace Form Nondegenerate: eq zero of trace mul
-- statement:
--   The Trace Form Nondegenerate construction uses the eq zero of trace mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanEqTopOfTraceEq.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanEqTopOfTraceEq.lean#L5-L10

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

theorem GlobalTheory.TraceFormNondegenerate.eq_zero_of_trace_mul {K : Type} [Field K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K)
    (h : ∀ Y : Matrix (Fin n) (Fin n) K, Matrix.trace (X * Y) = 0) : X = 0 := by sorry
