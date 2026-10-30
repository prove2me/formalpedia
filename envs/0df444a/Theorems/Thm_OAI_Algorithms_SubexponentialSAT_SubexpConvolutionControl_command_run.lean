-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpConvolutionControl_command_run
-- name    : OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.command_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:56:14.408238+00:00
-- url     : https://prove2.me/theorems/16ada01a-7877-41fc-a3d3-176b6cd3513b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.command_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.command_run` of [lean/OAI/Algorithms/SubexponentialSAT/SubexpConvolutionExecution.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpConvolutionExecution.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl`, with `open BitProgram StructuredCalls`):
--
--   ```lean
--   theorem command_run (pair : Code) (base : Store) (encode : C → List Bool)
--       (add mul : C → C → C) (D W pairCost : ℕ)
--       (hpair : PairSpec pair base encode add mul D pairCost)
--       (hencode : ∀ c, (encode c).length = W) (hwidth : (base 104).length = W)
--       (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
--       (w : Buffers) (P Q acc : List C) (hP : P.length = D) (hQ : Q.length = D)
--       (hlen : acc.length = D) (hleft : w 0 = encodeArray encode P)
--       (hright : w 1 = encodeArray encode Q) (hacc : w 2 = encodeArray encode acc)
--       (hcount : (w 5).length = D) (h4 : w 4 = [])
--       (h3 : w 3 = []) (h6 : w 6 = []) (h7 : w 7 = []) (h8 : w 8 = [])
--       (h9 : w 9 = []) (h10 : w 10 = []) :
--       ExecutesIn (command pair) (convolutionBudget D W pairCost) (buffers base w)
--         (buffers base (finishedBuffers w
--           (encodeArray encode (TruncatedConvolution.rows add mul Q 0 D P acc))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Buffers`, `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store`, `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.convolutionBudget` and `OAI.Algorithms.SubexponentialSAT.TruncatedConvolution.rows` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.encodeArray` (definitions bundle `OAIQ081S022` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Code` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.buffers` (definitions bundle `OAIQ081S028` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.finishedBuffers` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.command` (definitions bundle `OAIQ081S068` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.PairSpec` (definitions bundle `OAIQ081S081` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.mul_spec` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpConvolutionExecution.lean (declaration OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.command_run)

import Mathlib
import Definitions.Def_OAIQ081S068
import Definitions.Def_OAIQ081S081

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

variable {C : Type*}

theorem command_run (pair : Code) (base : Store) (encode : C → List Bool)
    (add mul : C → C → C) (D W pairCost : ℕ)
    (hpair : PairSpec pair base encode add mul D pairCost)
    (hencode : ∀ c, (encode c).length = W) (hwidth : (base 104).length = W)
    (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
    (w : Buffers) (P Q acc : List C) (hP : P.length = D) (hQ : Q.length = D)
    (hlen : acc.length = D) (hleft : w 0 = encodeArray encode P)
    (hright : w 1 = encodeArray encode Q) (hacc : w 2 = encodeArray encode acc)
    (hcount : (w 5).length = D) (h4 : w 4 = [])
    (h3 : w 3 = []) (h6 : w 6 = []) (h7 : w 7 = []) (h8 : w 8 = [])
    (h9 : w 9 = []) (h10 : w 10 = []) :
    ExecutesIn (command pair) (convolutionBudget D W pairCost) (buffers base w)
      (buffers base (finishedBuffers w
        (encodeArray encode (TruncatedConvolution.rows add mul Q 0 D P acc)))) := by
  sorry

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end
