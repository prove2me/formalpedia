-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader_localResult_nonoutput_length
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult_nonoutput_length
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:41:59.526139+00:00
-- url     : https://prove2.me/theorems/18ac24fc-0da1-441e-9fcd-efd9cefe951f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult_nonoutput_length: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult_nonoutput_length` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoaderCore.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoaderCore.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader`, with `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram`, `open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage`):
--
--   ```lean
--   theorem localResult_nonoutput_length (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
--       (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
--       (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
--       (i : Fin 768) (h650 : i≠650) (h651 : i≠651) (h652 : i≠652)
--       (h668 : i≠668) (h670 : i≠670) (h671 : i≠671) :
--       ((localResult a rp rm rs n N W z rows low raw shifted).stacks i).length ≤
--         (a.stacks i).length
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.Pair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult` (definitions bundle `OAIQ081S165` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.load_run_polynomial` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.load_run_polynomial` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoaderCore.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult_nonoutput_length)

import Mathlib
import Definitions.Def_OAIQ081S165

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem localResult_nonoutput_length (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 768) (h650 : i≠650) (h651 : i≠651) (h652 : i≠652)
    (h668 : i≠668) (h670 : i≠670) (h671 : i≠671) :
    ((localResult a rp rm rs n N W z rows low raw shifted).stacks i).length ≤
      (a.stacks i).length := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end
