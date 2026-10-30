-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_CofactorOuter_command_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter.command_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:09:58.042327+00:00
-- url     : https://prove2.me/theorems/803ea457-f143-4f1c-83f7-a3e7c5193c93
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter.command_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter.command_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramCofactorOuter.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramCofactorOuter.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram`, `open CRTLocalProgram (ServiceSpec LowFrame)`):
--
--   ```lean
--   theorem command_run {C : Type*} (encode : C → List Bool)
--       (multiply : Cmd 16 256) (mulOp : C → C → C) (K W J : ℕ)
--       (d : Data) (remaining processed : List C) (unit minusOne : C)
--       (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp K)
--       (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
--       (hr : d.stacks 257 = remaining.flatMap encode)
--       (hp : d.stacks 258 = processed.flatMap encode)
--       (hu : d.stacks 207 = encode unit) (hn : d.stacks 211 = encode minusOne)
--       (hJ : d.stacks 243 = List.replicate J true) (hwidth : (d.stacks 104).length = W)
--       (hc : ∀ i ∈ cleanPorts, d.stacks i = []) :
--       ∃ n ≤ budget (remaining.length + processed.length) K W J, ∃ rf,
--         Eval (command multiply) n d
--           ⟨rf, Function.update d.stacks 262
--             (encode ((remaining ++ processed).foldl (Cofactor.includeValue mulOp minusOne J) unit))⟩
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.localPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter.cleanPorts` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.includeValue` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter.budget` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.ServiceSpec` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter.command` (definitions bundle `OAIQ081S144` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.command_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramCofactorOuter.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter.command_run)

import Mathlib
import Definitions.Def_OAIQ081S144

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec LowFrame)

theorem command_run {C : Type*} (encode : C → List Bool)
    (multiply : Cmd 16 256) (mulOp : C → C → C) (K W J : ℕ)
    (d : Data) (remaining processed : List C) (unit minusOne : C)
    (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp K)
    (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
    (hr : d.stacks 257 = remaining.flatMap encode)
    (hp : d.stacks 258 = processed.flatMap encode)
    (hu : d.stacks 207 = encode unit) (hn : d.stacks 211 = encode minusOne)
    (hJ : d.stacks 243 = List.replicate J true) (hwidth : (d.stacks 104).length = W)
    (hc : ∀ i ∈ cleanPorts, d.stacks i = []) :
    ∃ n ≤ budget (remaining.length + processed.length) K W J, ∃ rf,
      Eval (command multiply) n d
        ⟨rf, Function.update d.stacks 262
          (encode ((remaining ++ processed).foldl (Cofactor.includeValue mulOp minusOne J) unit))⟩ := by
  sorry

end SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter

end OAI.Algorithms
end
