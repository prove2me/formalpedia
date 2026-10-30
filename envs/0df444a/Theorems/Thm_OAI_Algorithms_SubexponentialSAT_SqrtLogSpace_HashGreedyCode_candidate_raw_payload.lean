-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyCode_candidate_raw_payload
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.candidate_raw_payload
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:16:44.363098+00:00
-- url     : https://prove2.me/theorems/482dbd50-b552-4156-87c6-fa5ab1727d42
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.candidate_raw_payload: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.candidate_raw_payload` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCode.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCode.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode`, with `open SqrtLog`, `open scoped BigOperators`, `open HashGreedyCNF`):
--
--   ```lean
--   theorem candidate_raw_payload {m : ℕ} (hm : 0 < m) (depth rank : ℕ) :
--       (CodeRowsProgram.rowPayload (HashCandidates.digitWidth m) m
--         (raw m hm (HashGreedyCandidate.candidate m depth rank))).reverse =
--           HashGreedyCandidate.candidate m depth rank
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowPayload` (definitions bundle `OAIQ081S028` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.digitWidth` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.raw` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate.candidate` (definitions bundle `OAIQ081S115` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_history_raw_encoding` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_trial_word_raw_encoding` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCode.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.candidate_raw_payload)

import Mathlib
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

theorem candidate_raw_payload {m : ℕ} (hm : 0 < m) (depth rank : ℕ) :
    (CodeRowsProgram.rowPayload (HashCandidates.digitWidth m) m
      (raw m hm (HashGreedyCandidate.candidate m depth rank))).reverse =
        HashGreedyCandidate.candidate m depth rank := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode
end
