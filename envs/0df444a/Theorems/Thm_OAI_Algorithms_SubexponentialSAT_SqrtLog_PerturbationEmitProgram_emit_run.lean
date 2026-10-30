-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationEmitProgram_emit_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.emit_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:37:03.469265+00:00
-- url     : https://prove2.me/theorems/24908062-fab5-48c1-9b93-0cfcf605dc25
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.emit_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.emit_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationEmitProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationEmitProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl`):
--
--   ```lean
--   theorem emit_run (s : Store) (key coeff : List Bool)
--       (hk : s 222=key.reverse) (hc : s 228=coeff.reverse) :
--       ExecutesIn emitCommand (4*key.length+4*coeff.length+13) s
--         (Function.update (Function.update (Function.update s 222 []) 228 [])
--           217 (Encoding.frame key++Encoding.frame coeff++s 217))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.emitCommand` (definitions bundle `OAIQ081S135` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.frame` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.native_literal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.origin_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.command_run` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationEmitProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.emit_run)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S135

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

theorem emit_run (s : Store) (key coeff : List Bool)
    (hk : s 222=key.reverse) (hc : s 228=coeff.reverse) :
    ExecutesIn emitCommand (4*key.length+4*coeff.length+13) s
      (Function.update (Function.update (Function.update s 222 []) 228 [])
        217 (Encoding.frame key++Encoding.frame coeff++s 217)) := by
  sorry

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram

end OAI.Algorithms
end
