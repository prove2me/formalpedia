-- Prove2me | Theorems.Thm_GlobalTheory_TraceGram_adjugate_entry_mem
-- name    : GlobalTheory.TraceGram.adjugate_entry_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:10:49.59925+00:00
-- url     : https://prove2.me/theorems/ba2db0a4-ee53-4e5e-8efb-bf38ee53f17b
-- title:
--   Trace Gram: adjugate entry mem
-- statement:
--   The Trace Gram construction uses the adjugate entry mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EntryMemSubringOfTraceGramUnit.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EntryMemSubringOfTraceGramUnit.lean#L20-L27

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

theorem GlobalTheory.TraceGram.adjugate_entry_mem {K : Type} [Field K] (O : Subring K) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (hG : ∀ i j, G i j ∈ O) : ∀ i j, G.adjugate i j ∈ O := by sorry
