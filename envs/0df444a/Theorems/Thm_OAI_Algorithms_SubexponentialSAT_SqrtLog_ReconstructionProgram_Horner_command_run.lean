-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Horner_command_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner.command_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:10:41.421393+00:00
-- url     : https://prove2.me/theorems/9451601f-8d25-4662-ac15-1e87c6a6d4e5
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner.command_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner.command_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramHorner.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramHorner.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram`, `open CRTLocalProgram (ServiceSpec LowFrame)`):
--
--   ```lean
--   theorem command_run {C : Type*} (encode : C → List Bool)
--       (multiply add : Cmd 16 256) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
--       (d : Data) (P : List C) (point zero : C)
--       (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp Km)
--       (ha : ServiceSpec (d.stacks ∘ localPorts) encode add addOp Ka)
--       (hw : ∀ a, (encode a).length = W)
--       (hP : d.stacks 244 = HornerProgram.encodePolynomial encode P)
--       (hx : d.stacks 263 = encode point) (hz : d.stacks 104 = encode zero)
--       (hJ : (d.stacks 243).length = P.length)
--       (hc : ∀ i ∈ cleanPorts, d.stacks i = []) :
--       ∃ n ≤ budget P.length W Km Ka, ∃ rf,
--         Eval (command multiply add) n d
--           ⟨rf, Function.update (Function.update d.stacks 244 [])
--             264 (encode (HornerProgram.fold (HornerProgram.stepValue mulOp addOp point) P.reverse zero))⟩
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.encodePolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.fold` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.stepValue` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.localPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner.cleanPorts` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner.budget` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.ServiceSpec` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner.command` (definitions bundle `OAIQ081S144` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.command_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramHorner.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner.command_run)

import Mathlib
import Definitions.Def_OAIQ081S144

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec LowFrame)

theorem command_run {C : Type*} (encode : C → List Bool)
    (multiply add : Cmd 16 256) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (d : Data) (P : List C) (point zero : C)
    (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp Km)
    (ha : ServiceSpec (d.stacks ∘ localPorts) encode add addOp Ka)
    (hw : ∀ a, (encode a).length = W)
    (hP : d.stacks 244 = HornerProgram.encodePolynomial encode P)
    (hx : d.stacks 263 = encode point) (hz : d.stacks 104 = encode zero)
    (hJ : (d.stacks 243).length = P.length)
    (hc : ∀ i ∈ cleanPorts, d.stacks i = []) :
    ∃ n ≤ budget P.length W Km Ka, ∃ rf,
      Eval (command multiply add) n d
        ⟨rf, Function.update (Function.update d.stacks 244 [])
          264 (encode (HornerProgram.fold (HornerProgram.stepValue mulOp addOp point) P.reverse zero))⟩ := by
  sorry

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner

end OAI.Algorithms
end
