-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpNodeScanControl_command_run
-- name    : OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.command_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:56:42.936501+00:00
-- url     : https://prove2.me/theorems/5467b389-e0c4-45d5-b1f4-9d7ead2becf8
-- title:
--   OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.command_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.command_run` of [lean/OAI/Algorithms/SubexponentialSAT/SubexpNodeScanControl.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpNodeScanControl.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl`, with `open BitProgram StructuredCalls SubexpConvolutionControl`):
--
--   ```lean
--   theorem command_run (includeNode : Code) (base : Store)
--       (encode : C → List Bool) (encodeA : A → List Bool)
--       (negative : C → List Bool) (f : A → C → A) (K W : ℕ)
--       (hinclude : IncludeSpec includeNode base encode encodeA negative f K)
--       (hencode : ∀ c, (encode c).length = W) (hW : 0 < W)
--       (hnegative : ∀ c, (negative c).length ≤ W)
--       (hwidth : (base 104).length = W) (h121 : base 121 = []) (h122 : base 122 = [])
--       (cs : List C) (x : Cursor A) :
--       ExecutesIn (command includeNode) (cs.length * (K + 18 * W + 28) + 2)
--         (ready base encode encodeA cs x [] [])
--         (ready base encode encodeA [] (run f cs x) [] [])
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.Cursor` and `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.run` (definitions bundle `OAIQ081S022` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Code` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.command` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.IncludeSpec` and `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.ready` (definitions bundle `OAIQ081S081` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localCommand_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.scan_state_run` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpNodeScanControl.lean (declaration OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.command_run)

import Mathlib
import Definitions.Def_OAIQ081S081

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpNodeScanControl

open BitProgram StructuredCalls SubexpConvolutionControl

variable {A C : Type*}

theorem command_run (includeNode : Code) (base : Store)
    (encode : C → List Bool) (encodeA : A → List Bool)
    (negative : C → List Bool) (f : A → C → A) (K W : ℕ)
    (hinclude : IncludeSpec includeNode base encode encodeA negative f K)
    (hencode : ∀ c, (encode c).length = W) (hW : 0 < W)
    (hnegative : ∀ c, (negative c).length ≤ W)
    (hwidth : (base 104).length = W) (h121 : base 121 = []) (h122 : base 122 = [])
    (cs : List C) (x : Cursor A) :
    ExecutesIn (command includeNode) (cs.length * (K + 18 * W + 28) + 2)
      (ready base encode encodeA cs x [] [])
      (ready base encode encodeA [] (run f cs x) [] []) := by
  sorry

end SubexponentialSAT.SubexpNodeScanControl

end OAI.Algorithms
end
