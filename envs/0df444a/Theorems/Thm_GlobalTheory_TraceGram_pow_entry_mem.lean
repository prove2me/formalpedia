-- Prove2me | Theorems.Thm_GlobalTheory_TraceGram_pow_entry_mem
-- name    : GlobalTheory.TraceGram.pow_entry_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:10:55.755141+00:00
-- url     : https://prove2.me/theorems/c0ff236b-f82b-49f3-af38-e58efb19b223
-- title:
--   Trace Gram: pow entry mem
-- statement:
--   The Trace Gram construction uses the pow entry mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EntryMemSubringOfTraceGramUnit.lean#L6-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EntryMemSubringOfTraceGramUnit.lean#L6-L18

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

theorem GlobalTheory.TraceGram.pow_entry_mem {K : Type} [Field K] (O : Subring K) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K) (hg : ∀ i j, g i j ∈ O) (k : ℕ) : ∀ i j, (g ^ k) i j ∈ O := by sorry
