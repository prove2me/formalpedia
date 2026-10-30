-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HornerProgram_command_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.command_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:30:23.812355+00:00
-- url     : https://prove2.me/theorems/cb3f9279-88bd-40ba-a42c-abffe1683103
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.command_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.command_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HornerProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HornerProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl`, `open CRTLocalProgram (ServiceSpec serviceSpec_frame lowFrame_refl lowFrame_update)`):
--
--   ```lean
--   theorem command_run {C : Type*} (base : Store) (encode : C → List Bool)
--       (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
--       (hm : ServiceSpec base encode multiply mulOp Km)
--       (ha : ServiceSpec base encode add addOp Ka)
--       (hwidth : ∀ a, (encode a).length = W)
--       (P : List C) (x seed : C)
--       (hP : base 246 = encodePolynomial encode P) (hx : base 247 = encode x)
--       (hseed : base 240 = encode seed) (hcount : (base 248).length = P.length)
--       (hw : (base 250).length = W)
--       (h120 : base 120 = []) (h241 : base 241 = []) (h244 : base 244 = [])
--       (h245 : base 245 = []) (h251 : base 251 = []) (h252 : base 252 = []) :
--       ExecutesIn (command multiply add) (budget P.length W Km Ka) base
--         (Function.update (Function.update (Function.update base 246 [])
--           240 (encode (fold (stepValue mulOp addOp x) P.reverse seed))) 248 [])
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.encodePolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.fold` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.stepValue` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Code` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.ServiceSpec` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.command` (definitions bundle `OAIQ081S119` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shift_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.step_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner.command_run` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HornerProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.command_run)

import Mathlib
import Definitions.Def_OAIQ081S119

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec serviceSpec_frame lowFrame_refl lowFrame_update)

theorem command_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length = W)
    (P : List C) (x seed : C)
    (hP : base 246 = encodePolynomial encode P) (hx : base 247 = encode x)
    (hseed : base 240 = encode seed) (hcount : (base 248).length = P.length)
    (hw : (base 250).length = W)
    (h120 : base 120 = []) (h241 : base 241 = []) (h244 : base 244 = [])
    (h245 : base 245 = []) (h251 : base 251 = []) (h252 : base 252 = []) :
    ExecutesIn (command multiply add) (budget P.length W Km Ka) base
      (Function.update (Function.update (Function.update base 246 [])
        240 (encode (fold (stepValue mulOp addOp x) P.reverse seed))) 248 []) := by
  sorry

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end
