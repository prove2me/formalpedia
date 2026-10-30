-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryCount_branch_kept_of_stream
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.branch_kept_of_stream
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:25:31.524063+00:00
-- url     : https://prove2.me/theorems/cf06e86b-4142-4c79-b594-3886a7fc3758
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.branch_kept_of_stream: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.branch_kept_of_stream` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryCount.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryCount.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount`, with `open OAI BitProgram StructuredCalls SqrtLog LeafProgram`, `open HighQueryAdapter`):
--
--   ```lean
--   theorem branch_kept_of_stream {a middle b : Data} {querySteps branchSteps : ℕ}
--       (he : Eval QueryStreamProgram.command querySteps (copiedHighCounter a) middle)
--       (hb : Eval HighQueryProgram.branch branchSteps a b)
--       (hs : a.stacks 791=[])
--       (hf : ∀ i,HashMarkedReturn.kept i=true →
--         middle.stacks i=(copiedHighCounter a).stacks i) :
--       ∀ i,HashMarkedReturn.kept i=true → b.stacks i=a.stacks i
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.kept` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.copiedHighCounter` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.Data` (definitions bundle `OAIQ081S174` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.branch` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.command` (definitions bundle `OAIQ081S193` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryCount.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.branch_kept_of_stream)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S193

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount

open OAI BitProgram StructuredCalls SqrtLog LeafProgram
open HighQueryAdapter

theorem branch_kept_of_stream {a middle b : Data} {querySteps branchSteps : ℕ}
    (he : Eval QueryStreamProgram.command querySteps (copiedHighCounter a) middle)
    (hb : Eval HighQueryProgram.branch branchSteps a b)
    (hs : a.stacks 791=[])
    (hf : ∀ i,HashMarkedReturn.kept i=true →
      middle.stacks i=(copiedHighCounter a).stacks i) :
    ∀ i,HashMarkedReturn.kept i=true → b.stacks i=a.stacks i := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount
end
