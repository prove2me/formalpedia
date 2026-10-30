-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Cofactor_scan_state_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.scan_state_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:38:18.889925+00:00
-- url     : https://prove2.me/theorems/faba0393-7f29-4928-a5bd-39ed8a1242ed
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.scan_state_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.scan_state_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramCofactorState.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramCofactorState.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl`, `open CRTLocalProgram (LowFrame ServiceSpec)`):
--
--   ```lean
--   theorem scan_state_run {C : Type*} (base : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (encode : C → List Bool)
--       (multiply : Code) (mul : C → C → C) (minusOne : C) (K W J : ℕ)
--       (hspec : ServiceSpec base encode multiply mul K)
--       (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
--       (s : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (hf : LowFrame base s) (cs : List C) (unit : C)
--       (hm : s 211 = encode minusOne) (hj : s 243 = List.replicate J true)
--       (hwidth : (s 104).length = W)
--       (hstream : s 215 = cs.flatMap encode) (hunit : s 240 = encode unit)
--       (hclean : ∀ j ∈ ([120,121,122,217,218,219,223,229,241,244,245,246] : List (Fin 256)), s j = []) :
--       ExecutesIn (scan multiply) (cs.length * (includeBudget K W J + 18 * W + 28) + 2) s
--         (Function.update (Function.update s 215 [])
--           240 (encode (cs.foldl (includeValue mul minusOne J) unit)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.LowFrame` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.includeBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.includeValue` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Code` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.ServiceSpec` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.scan` (definitions bundle `OAIQ081S127` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter.command_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramCofactorState.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.scan_state_run)

import Mathlib
import Definitions.Def_OAIQ081S127

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (LowFrame ServiceSpec)

theorem scan_state_run {C : Type*} (base : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (encode : C → List Bool)
    (multiply : Code) (mul : C → C → C) (minusOne : C) (K W J : ℕ)
    (hspec : ServiceSpec base encode multiply mul K)
    (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
    (s : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (hf : LowFrame base s) (cs : List C) (unit : C)
    (hm : s 211 = encode minusOne) (hj : s 243 = List.replicate J true)
    (hwidth : (s 104).length = W)
    (hstream : s 215 = cs.flatMap encode) (hunit : s 240 = encode unit)
    (hclean : ∀ j ∈ ([120,121,122,217,218,219,223,229,241,244,245,246] : List (Fin 256)), s j = []) :
    ExecutesIn (scan multiply) (cs.length * (includeBudget K W J + 18 * W + 28) + 2) s
      (Function.update (Function.update s 215 [])
        240 (encode (cs.foldl (includeValue mul minusOne J) unit))) := by
  sorry

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

end OAI.Algorithms
end
