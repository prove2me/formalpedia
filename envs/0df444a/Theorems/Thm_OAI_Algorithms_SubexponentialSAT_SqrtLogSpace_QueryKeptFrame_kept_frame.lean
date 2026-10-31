-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryKeptFrame_kept_frame
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.kept_frame
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:32:17.870234+00:00
-- url     : https://prove2.me/theorems/8b44c8b6-e347-427e-a35f-60bc57ed7848
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.kept_frame: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.kept_frame` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryKeptFrame.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryKeptFrame.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame`, with `open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay`, `open SignatureTupleProgram SignatureTupleNative`):
--
--   ```lean
--   theorem kept_frame {steps : ℕ} {a b : State 40 896}
--       (he : Eval QueryStreamProgram.command steps a b)
--       (hsource : ∀ i ∈ ([700,701,707,708,709] : List (Fin 896)), b.stacks i = a.stacks i)
--       (i : Fin 896) (hi : HashMarkedReturn.kept i = true) : b.stacks i = a.stacks i
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.kept` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.command` (definitions bundle `OAIQ081S193` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryKeptFrame.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.kept_frame)

import Mathlib
import Definitions.Def_OAIQ081S193

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SignatureTupleProgram SignatureTupleNative

theorem kept_frame {steps : ℕ} {a b : State 40 896}
    (he : Eval QueryStreamProgram.command steps a b)
    (hsource : ∀ i ∈ ([700,701,707,708,709] : List (Fin 896)), b.stacks i = a.stacks i)
    (i : Fin 896) (hi : HashMarkedReturn.kept i = true) : b.stacks i = a.stacks i := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame
end
