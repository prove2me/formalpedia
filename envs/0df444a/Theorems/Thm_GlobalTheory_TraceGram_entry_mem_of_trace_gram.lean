-- Prove2me | Theorems.Thm_GlobalTheory_TraceGram_entry_mem_of_trace_gram
-- name    : GlobalTheory.TraceGram.entry_mem_of_trace_gram
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:42:33.765494+00:00
-- url     : https://prove2.me/theorems/2964c9ce-1a5e-4e15-9783-2e113c138b1e
-- title:
--   Trace Gram: entry mem of trace gram
-- statement:
--   The Trace Gram construction uses the entry mem of trace gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EntryMemSubringOfTraceGramUnit.lean#L29-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EntryMemSubringOfTraceGramUnit.lean#L29-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntryMemSubringOfTraceGramUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.TraceGram

theorem GlobalTheory.TraceGram.entry_mem_of_trace_gram : ∀ {K : Type} [Field K] (O : Subring K) {n : ℕ} (g x : Matrix (Fin n) (Fin n) K) (c : Fin n → K),
    x = ∑ i, c i • g ^ (i : ℕ) → (∀ i j, g i j ∈ O) → (∀ j : Fin n, (x * g ^ (j : ℕ)).trace ∈ O) →
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 →
    ((Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det)⁻¹ ∈ O → ∀ i j, x i j ∈ O := by sorry
