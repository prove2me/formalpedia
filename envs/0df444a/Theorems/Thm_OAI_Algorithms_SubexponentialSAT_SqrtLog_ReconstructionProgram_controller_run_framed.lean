-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_controller_run_framed
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controller_run_framed
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:39:24.526769+00:00
-- url     : https://prove2.me/theorems/d602358d-8e70-4ae2-92dc-280f33fc08ea
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controller_run_framed: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controller_run_framed` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramFrame.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramFrame.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram`):
--
--   ```lean
--   theorem controller_run_framed {I A R : Type*} [AddMonoid R]
--       (encode : I → List Bool) (jet : I → List Bool) (encodeAcc : A → List Bool)
--       (value : A → R) (term : I → R) (middle : Code)
--       (d : Data) (D K : ℕ) (full : List I) (zero : A)
--       (hd : d.stacks 243 = List.replicate D true)
--       (hclean : ∀ j ∈ initialCleanPorts, d.stacks j = [])
--       (hwidth : ∀ i, (encode i).length = (d.stacks 280).length)
--       (hjet : ∀ i, (jet i).length = D * ((d.stacks 280).length))
--       (hpos : 0 < (d.stacks 280).length)
--       (hnodes : d.stacks 256 = full.flatMap encode)
--       (hjets : d.stacks 265 = full.flatMap jet)
--       (hz : encodeAcc zero = d.stacks 280)
--       (hvz : value zero = 0)
--       (hmid : ∀ exponent, BinaryArithmetic.toNat exponent = D → exponent.length ≤ D →
--         ∀ processed remaining item acc, full = processed.reverse ++ item :: remaining →
--         ∀ rr, ∃ n ≤ K, ∃ rf b,
--           Eval middle n
--             (sweepState rr (initializedStacks d D exponent)
--               (loadedReady encode jet encodeAcc processed remaining item acc))
--             (sweepState rf (initializedStacks d D exponent)
--               (loadedReady encode jet encodeAcc processed remaining item b)) ∧
--           value b = value acc + term item) :
--       ∃ n ≤ controllerBudget (d.stacks 280).length D full.length K,
--         ∃ (out : Data) (b : A), Eval (controller middle) n d out ∧
--           out.stacks = Function.update d.stacks 261 (encodeAcc b) ∧ value b = (full.map term).sum
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.initialCleanPorts` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controllerBudget` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.loadedReady` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.Code` and `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.initializedStacks` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.sweepState` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controller` (definitions bundle `OAIQ081S127` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.command_value` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramFrame.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controller_run_framed)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S114
import Definitions.Def_OAIQ081S115
import Definitions.Def_OAIQ081S127

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram

theorem controller_run_framed {I A R : Type*} [AddMonoid R]
    (encode : I → List Bool) (jet : I → List Bool) (encodeAcc : A → List Bool)
    (value : A → R) (term : I → R) (middle : Code)
    (d : Data) (D K : ℕ) (full : List I) (zero : A)
    (hd : d.stacks 243 = List.replicate D true)
    (hclean : ∀ j ∈ initialCleanPorts, d.stacks j = [])
    (hwidth : ∀ i, (encode i).length = (d.stacks 280).length)
    (hjet : ∀ i, (jet i).length = D * ((d.stacks 280).length))
    (hpos : 0 < (d.stacks 280).length)
    (hnodes : d.stacks 256 = full.flatMap encode)
    (hjets : d.stacks 265 = full.flatMap jet)
    (hz : encodeAcc zero = d.stacks 280)
    (hvz : value zero = 0)
    (hmid : ∀ exponent, BinaryArithmetic.toNat exponent = D → exponent.length ≤ D →
      ∀ processed remaining item acc, full = processed.reverse ++ item :: remaining →
      ∀ rr, ∃ n ≤ K, ∃ rf b,
        Eval middle n
          (sweepState rr (initializedStacks d D exponent)
            (loadedReady encode jet encodeAcc processed remaining item acc))
          (sweepState rf (initializedStacks d D exponent)
            (loadedReady encode jet encodeAcc processed remaining item b)) ∧
        value b = value acc + term item) :
    ∃ n ≤ controllerBudget (d.stacks 280).length D full.length K,
      ∃ (out : Data) (b : A), Eval (controller middle) n d out ∧
        out.stacks = Function.update d.stacks 261 (encodeAcc b) ∧ value b = (full.map term).sum := by
  sorry

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end
