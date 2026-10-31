-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram_Rescan_prepareKey_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.prepareKey_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:41:57.192101+00:00
-- url     : https://prove2.me/theorems/6fa275d1-0f10-4552-946b-2a714343a64b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.prepareKey_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.prepareKey_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/AttainedSignatureRescan.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/AttainedSignatureRescan.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan`, with `open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram`):
--
--   ```lean
--   theorem prepareKey_eval (regs : Fin 16 → Bool) (W : List Bool)
--       (rows : List (List (List Bool))) (candidate predecessor : List Bool) (fresh : Bool)
--       (hlen : ∀ row ∈ rows, row.length = candidate.length) :
--       ∃ n ≤ cost W candidate rows + 9 * candidate.length +
--           9 * (signatureValue W candidate rows).length + 17, ∃ out,
--         Eval prepareKey n (workState regs W rows candidate [] predecessor [] fresh [] [])
--           (workState out W rows candidate (signatureValue W candidate rows)
--             predecessor [] fresh [] [])
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.signatureValue` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.cost` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.workState` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.prepareKey` (definitions bundle `OAIQ081S136` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.candidate_stack_bound` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge.probe_run_space` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/AttainedSignatureRescan.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.prepareKey_eval)

import Mathlib
import Definitions.Def_OAIQ081S136

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace Rescan

theorem prepareKey_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate predecessor : List Bool) (fresh : Bool)
    (hlen : ∀ row ∈ rows, row.length = candidate.length) :
    ∃ n ≤ cost W candidate rows + 9 * candidate.length +
        9 * (signatureValue W candidate rows).length + 17, ∃ out,
      Eval prepareKey n (workState regs W rows candidate [] predecessor [] fresh [] [])
        (workState out W rows candidate (signatureValue W candidate rows)
          predecessor [] fresh [] []) := by
  sorry

end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end
