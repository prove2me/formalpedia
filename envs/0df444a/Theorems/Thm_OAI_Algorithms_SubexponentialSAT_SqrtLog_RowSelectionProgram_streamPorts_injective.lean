-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_RowSelectionProgram_streamPorts_injective
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.streamPorts_injective
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:33:48.217921+00:00
-- url     : https://prove2.me/theorems/95220964-061d-4f84-a02b-f7d05bac9097
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.streamPorts_injective: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.streamPorts_injective` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RowSelectionProgramStream.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RowSelectionProgramStream.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram`):
--
--   ```lean
--   theorem streamPorts_injective : Function.Injective streamPorts
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.streamPorts` (definitions bundle `OAIQ081S011` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.addEntry_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.accumulate_eval_total` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RowSelectionProgramStream.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.streamPorts_injective)

import Mathlib
import Definitions.Def_OAIQ081S011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem streamPorts_injective : Function.Injective streamPorts := by
  sorry

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end
