-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_portStep_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portStep_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:25:08.68018+00:00
-- url     : https://prove2.me/theorems/1c0e4d71-d649-4366-8f31-b440d85d232e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portStep_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portStep_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramPort.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramPort.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic`):
--
--   ```lean
--   theorem portStep_eval (d : Data) (a b : Bool) (qt st : List Bool)
--       (pairs : List (Bool × Bool))
--       (hq : d.stacks 0=Cell.frame a b++qt)
--       (hs : d.stacks 1=Shift.frames (pairs.map Prod.snd)++st)
--       (hv : d.stacks 2=pairs.map Prod.fst)
--       (h17 : d.stacks 17=[]) (h18 : d.stacks 18=[]) (h19 : d.stacks 19=[])
--       (h20 : d.stacks 20=[]) (h21 : d.stacks 21=[])
--       (h22 : d.stacks 22=[]) (h23 : d.stacks 23=[])
--       (h24 : d.stacks 24=[]) (h25 : d.stacks 25=[]) (h41 : d.stacks 41=[])
--       (ha : ∀ i, d.stacks (arithmeticWork i)=[])
--       (hc : ∀ i : Fin 8, 2 ≤ i.val → d.stacks (compareStacks i)=[])
--       (hcap : 3*BinaryArithmetic.toNat (d.stacks 4) ≤ 2^(d.stacks 5).length) :
--       ∃ n rf, Eval portStep n d ⟨rf,portStacks d qt st (portAccum d a b pairs)⟩ ∧
--         n ≤ 2000*(portWidth d+1)^2 ∧
--         (∀ i : Fin 16, 8 ≤ i.val → rf i=coefficientRegs d.regs a b i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell.frame` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.arithmeticWork`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.coefficientRegs` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.compareStacks` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.frames` (definitions bundle `OAIQ081S029` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Data` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portAccum`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portStep` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portWidth` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.localStep_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramPort.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portStep_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S118

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem portStep_eval (d : Data) (a b : Bool) (qt st : List Bool)
    (pairs : List (Bool × Bool))
    (hq : d.stacks 0=Cell.frame a b++qt)
    (hs : d.stacks 1=Shift.frames (pairs.map Prod.snd)++st)
    (hv : d.stacks 2=pairs.map Prod.fst)
    (h17 : d.stacks 17=[]) (h18 : d.stacks 18=[]) (h19 : d.stacks 19=[])
    (h20 : d.stacks 20=[]) (h21 : d.stacks 21=[])
    (h22 : d.stacks 22=[]) (h23 : d.stacks 23=[])
    (h24 : d.stacks 24=[]) (h25 : d.stacks 25=[]) (h41 : d.stacks 41=[])
    (ha : ∀ i, d.stacks (arithmeticWork i)=[])
    (hc : ∀ i : Fin 8, 2 ≤ i.val → d.stacks (compareStacks i)=[])
    (hcap : 3*BinaryArithmetic.toNat (d.stacks 4) ≤ 2^(d.stacks 5).length) :
    ∃ n rf, Eval portStep n d ⟨rf,portStacks d qt st (portAccum d a b pairs)⟩ ∧
      n ≤ 2000*(portWidth d+1)^2 ∧
      (∀ i : Fin 16, 8 ≤ i.val → rf i=coefficientRegs d.regs a b i) := by
  sorry

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end
