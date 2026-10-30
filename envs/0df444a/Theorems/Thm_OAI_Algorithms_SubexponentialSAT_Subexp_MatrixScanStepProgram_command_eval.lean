-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_MatrixScanStepProgram_command_eval
-- name    : OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram.command_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:55:52.586773+00:00
-- url     : https://prove2.me/theorems/63cc46c3-2081-4e1c-b2d7-3c85f4e7e9e5
-- title:
--   OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram.command_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram.command_eval` of [lean/OAI/Algorithms/SubexponentialSAT/Subexp/MatrixScanStepProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/MatrixScanStepProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram`, with `open BitProgram StructuredCalls StackRoutines`):
--
--   ```lean
--   theorem command_eval (a : Data) (words rests : Fin 4 → List Bool)
--       (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (h4 : a.stacks 4 = [])
--       (h10 : a.stacks 10 = []) (h11 : a.stacks 11 = []) (h12 : a.stacks 12 = [])
--       (hd : ∀ i, a.stacks (MatrixColorReadProgram.target i) = [])
--       (hs : ∀ i, a.stacks (MatrixColorReadProgram.source i) = words i ++ rests i)
--       (hlen : ∀ i, (words i).length = (a.stacks 21).length) :
--       ∃ n ≤ 208 * (a.stacks 21).length + 147,
--         Eval command n a (output a words rests)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixColorReadProgram.source` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixColorReadProgram.target` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram.Data` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram.command` (definitions bundle `OAIQ081S073` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram.output` (definitions bundle `OAIQ081S081` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Scan.scanStage_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/MatrixScanStepProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram.command_eval)

import Mathlib
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S081

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.Subexp.MatrixScanStepProgram

open BitProgram StructuredCalls StackRoutines

theorem command_eval (a : Data) (words rests : Fin 4 → List Bool)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (h4 : a.stacks 4 = [])
    (h10 : a.stacks 10 = []) (h11 : a.stacks 11 = []) (h12 : a.stacks 12 = [])
    (hd : ∀ i, a.stacks (MatrixColorReadProgram.target i) = [])
    (hs : ∀ i, a.stacks (MatrixColorReadProgram.source i) = words i ++ rests i)
    (hlen : ∀ i, (words i).length = (a.stacks 21).length) :
    ∃ n ≤ 208 * (a.stacks 21).length + 147,
      Eval command n a (output a words rests) := by
  sorry

end SubexponentialSAT.Subexp.MatrixScanStepProgram

end OAI.Algorithms
end
