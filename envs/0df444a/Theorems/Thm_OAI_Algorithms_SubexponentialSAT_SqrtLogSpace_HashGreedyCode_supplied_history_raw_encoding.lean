-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyCode_supplied_history_raw_encoding
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_history_raw_encoding
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:17:46.54297+00:00
-- url     : https://prove2.me/theorems/582cefad-d823-490b-9376-4006bce4aa3e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_history_raw_encoding: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_history_raw_encoding` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCode.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCode.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode`, with `open SqrtLog`, `open scoped BigOperators`, `open HashGreedyCNF`):
--
--   ```lean
--   theorem supplied_history_raw_encoding {n m B : ℕ}
--       (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
--       (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B) (rounds : ℕ) :
--       HashGreedyProgram.encodedHistory
--         (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds) =
--       HashScopeProgram.RawTable.inputBits (HashCandidates.digitWidth m)
--         ((history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.inputBits` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.digitWidth` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.initial` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.raw` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.encodedHistory` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Clause` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.accepted_entry` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCode.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_history_raw_encoding)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode

open SqrtLog
open scoped BigOperators
open HashGreedyCNF

noncomputable section

theorem supplied_history_raw_encoding {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B) (rounds : ℕ) :
    HashGreedyProgram.encodedHistory
      (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds) =
    HashScopeProgram.RawTable.inputBits (HashCandidates.digitWidth m)
      ((history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)) := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode
end
