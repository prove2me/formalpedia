-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Middle_command_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.command_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:11:18.907191+00:00
-- url     : https://prove2.me/theorems/d83d2151-cf2b-4917-804d-7f9c4ae5d1a7
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.command_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.command_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramMiddle.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramMiddle.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram`, `open CRTLocalProgram (LowFrame ServiceSpec)`):
--
--   ```lean
--   theorem command_run {C : Type*} (encode : C → List Bool)
--       (localCode multiply add : Cmd 16 256) (mulOp addOp : C → C → C)
--       (Km Ka Kl W J : ℕ) (d : Data) (remaining processed correction : List C)
--       (unit minusOne zero node acc : C)
--       (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp Km)
--       (ha : ServiceSpec (d.stacks ∘ localPorts) encode add addOp Ka)
--       (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
--       (hr : d.stacks 257 = remaining.flatMap encode) (hp : d.stacks 258 = processed.flatMap encode)
--       (hu : d.stacks 207 = encode unit) (hn : d.stacks 211 = encode minusOne)
--       (hz : d.stacks 104 = encode zero) (hx : d.stacks 259 = encode node)
--       (hacc : d.stacks 261 = encode acc) (hJ : d.stacks 243 = List.replicate J true)
--       (hcorr : correction.length = J) (h277 : (d.stacks 277).length = J * W)
--       (hc : ∀ i ∈ cleanPorts, d.stacks i = [])
--       (hlocal : SubexpConvolutionControl.ExecutesIn localCode Kl
--         ((Local.prepared d).stacks ∘ localPorts)
--         (Function.update ((Local.prepared d).stacks ∘ localPorts) 244
--           (HornerProgram.encodePolynomial encode correction))) :
--       ∃ n ≤ budget (remaining.length + processed.length) J W Km Ka Kl, ∃ rf,
--         Eval (command localCode multiply add) n d
--           ⟨rf, Function.update d.stacks 261
--             (encode (nodeValue mulOp addOp minusOne zero unit node acc J remaining processed correction))⟩
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.encodePolynomial` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.localPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.cleanPorts` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.budget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.nodeValue` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.ServiceSpec` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Local.prepared` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.command` (definitions bundle `OAIQ081S144` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.iteration_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramMiddle.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.command_run)

import Mathlib
import Definitions.Def_OAIQ081S144

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (LowFrame ServiceSpec)

theorem command_run {C : Type*} (encode : C → List Bool)
    (localCode multiply add : Cmd 16 256) (mulOp addOp : C → C → C)
    (Km Ka Kl W J : ℕ) (d : Data) (remaining processed correction : List C)
    (unit minusOne zero node acc : C)
    (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp Km)
    (ha : ServiceSpec (d.stacks ∘ localPorts) encode add addOp Ka)
    (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
    (hr : d.stacks 257 = remaining.flatMap encode) (hp : d.stacks 258 = processed.flatMap encode)
    (hu : d.stacks 207 = encode unit) (hn : d.stacks 211 = encode minusOne)
    (hz : d.stacks 104 = encode zero) (hx : d.stacks 259 = encode node)
    (hacc : d.stacks 261 = encode acc) (hJ : d.stacks 243 = List.replicate J true)
    (hcorr : correction.length = J) (h277 : (d.stacks 277).length = J * W)
    (hc : ∀ i ∈ cleanPorts, d.stacks i = [])
    (hlocal : SubexpConvolutionControl.ExecutesIn localCode Kl
      ((Local.prepared d).stacks ∘ localPorts)
      (Function.update ((Local.prepared d).stacks ∘ localPorts) 244
        (HornerProgram.encodePolynomial encode correction))) :
    ∃ n ≤ budget (remaining.length + processed.length) J W Km Ka Kl, ∃ rf,
      Eval (command localCode multiply add) n d
        ⟨rf, Function.update d.stacks 261
          (encode (nodeValue mulOp addOp minusOne zero unit node acc J remaining processed correction))⟩ := by
  sorry

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

end OAI.Algorithms
end
