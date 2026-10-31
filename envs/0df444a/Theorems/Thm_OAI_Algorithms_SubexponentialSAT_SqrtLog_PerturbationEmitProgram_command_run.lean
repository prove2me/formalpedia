-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationEmitProgram_command_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.command_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:36:58.984639+00:00
-- url     : https://prove2.me/theorems/5b85796d-40aa-480b-967d-a62b2a6fcca1
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.command_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.command_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationEmitProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationEmitProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl`):
--
--   ```lean
--   theorem command_run (s : Store) (mask : List Bool) (W : ℕ)
--       (cs : List (List Bool)) (hc : ∀ c ∈ cs,c.length=W)
--       (hs : s 240=array cs) (hJ : s 213=List.replicate cs.length true)
--       (hw : (s 211).length=W) (hm : s 214=mask)
--       (h120 : s 120=[]) (h221 : s 221=[]) (h222 : s 222=[]) (h223 : s 223=[])
--       (h224 : s 224=[]) (h225 : s 225=[]) (h226 : s 226=[]) (h227 : s 227=[]) (h228 : s 228=[]) :
--       ExecutesIn command (budget cs.length mask.length W) s
--         (Function.update (Function.update s 240 []) 217 (emitted mask 1 cs.tail (s 217)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.array` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.budget` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.emitted` (definitions bundle `OAIQ081S135` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_coordinate_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationEmitProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.command_run)

import Mathlib
import Definitions.Def_OAIQ081S135

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

theorem command_run (s : Store) (mask : List Bool) (W : ℕ)
    (cs : List (List Bool)) (hc : ∀ c ∈ cs,c.length=W)
    (hs : s 240=array cs) (hJ : s 213=List.replicate cs.length true)
    (hw : (s 211).length=W) (hm : s 214=mask)
    (h120 : s 120=[]) (h221 : s 221=[]) (h222 : s 222=[]) (h223 : s 223=[])
    (h224 : s 224=[]) (h225 : s 225=[]) (h226 : s 226=[]) (h227 : s 227=[]) (h228 : s 228=[]) :
    ExecutesIn command (budget cs.length mask.length W) s
      (Function.update (Function.update s 240 []) 217 (emitted mask 1 cs.tail (s 217))) := by
  sorry

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram

end OAI.Algorithms
end
