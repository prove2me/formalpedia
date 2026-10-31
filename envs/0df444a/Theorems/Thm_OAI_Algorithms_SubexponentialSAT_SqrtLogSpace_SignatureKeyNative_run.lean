-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureKeyNative_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:49:36.423629+00:00
-- url     : https://prove2.me/theorems/3add3b34-cc3b-4f0b-8cf4-ea4d4697cd30
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureKeyNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureKeyNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative`, with `open BitProgram StructuredCalls AttainedSignatureProgram`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport`):
--
--   ```lean
--   theorem run (a : State 40 896) (W bits : List Bool)
--       (rows : List (List (List Bool))) (ready : Ready a W bits rows)
--       (hlen : ∀ row ∈ rows, row.length = bits.length) (frameBound : ℕ)
--       (hframe : ∀ i, (a.stacks i).length ≤ frameBound) :
--       ∃ n ≤ cost W bits rows + 1, ∃ out,
--         Eval command n a (outputState a out W bits rows) ∧
--         Trace machine n (a.withPC (some machine.entry))
--           ((outputState a out W bits rows).withPC none) ∧
--         ∀ prefixSteps intermediate, prefixSteps ≤ n →
--           Trace machine prefixSteps (a.withPC (some machine.entry)) intermediate →
--           ∀ i, (intermediate.stacks i).length ≤
--             max (16 * (W.length + bits.length + (words (rows.map words)).length) +
--               cost W bits rows + 1) frameBound
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.cost` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.machine` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.Ready` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.outputState` (definitions bundle `OAIQ081S137` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.prepare_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureKeyNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.run)

import Mathlib
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S137

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative

open BitProgram StructuredCalls AttainedSignatureProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

theorem run (a : State 40 896) (W bits : List Bool)
    (rows : List (List (List Bool))) (ready : Ready a W bits rows)
    (hlen : ∀ row ∈ rows, row.length = bits.length) (frameBound : ℕ)
    (hframe : ∀ i, (a.stacks i).length ≤ frameBound) :
    ∃ n ≤ cost W bits rows + 1, ∃ out,
      Eval command n a (outputState a out W bits rows) ∧
      Trace machine n (a.withPC (some machine.entry))
        ((outputState a out W bits rows).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace machine prefixSteps (a.withPC (some machine.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          max (16 * (W.length + bits.length + (words (rows.map words)).length) +
            cost W bits rows + 1) frameBound := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative
end
