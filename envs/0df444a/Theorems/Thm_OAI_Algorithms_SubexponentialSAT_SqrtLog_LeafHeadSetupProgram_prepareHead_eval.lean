-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadSetupProgram_prepareHead_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.prepareHead_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:02:56.634324+00:00
-- url     : https://prove2.me/theorems/cd492e96-fbc1-48b7-a351-5e11aa3311b5
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.prepareHead_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.prepareHead_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHeadSetupProgramPrepare.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHeadSetupProgramPrepare.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`):
--
--   ```lean
--   theorem prepareHead_eval (a : Data) (n N : ℕ) (rows : List (List Bool))
--       (low : List Bool) (W z : ℕ)
--       (hn : a.stacks 128=unary n) (hN : a.stacks 129=unary N)
--       (hlow : a.stacks 134=low) (hz : a.stacks 649=unary z)
--       (hrows : a.stacks 133=rows.flatten) (hW : a.stacks 132=unary W)
--       (hw : ∀ row∈rows,row.length=W) (hsize : n+N ≤ rows.length) :
--       ∃ regs t,t ≤ prepareHeadCost a regs n N rows low W z ∧
--         Eval prepareHead t a (preparedHead a regs n N rows low W z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.prepareHead`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.prepareHeadCost` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.preparedHead` (definitions bundle `OAIQ081S144` of this split).
--
--   **Used by.** The proofs of `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad_load_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.native_leafFrom_run_space` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHeadSetupProgramPrepare.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.prepareHead_eval)

import Mathlib
import Definitions.Def_OAIQ081S144

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem prepareHead_eval (a : Data) (n N : ℕ) (rows : List (List Bool))
    (low : List Bool) (W z : ℕ)
    (hn : a.stacks 128=unary n) (hN : a.stacks 129=unary N)
    (hlow : a.stacks 134=low) (hz : a.stacks 649=unary z)
    (hrows : a.stacks 133=rows.flatten) (hW : a.stacks 132=unary W)
    (hw : ∀ row∈rows,row.length=W) (hsize : n+N ≤ rows.length) :
    ∃ regs t,t ≤ prepareHeadCost a regs n N rows low W z ∧
      Eval prepareHead t a (preparedHead a regs n N rows low W z) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end
