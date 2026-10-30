-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader_localResult_outputs
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult_outputs
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:42:05.587176+00:00
-- url     : https://prove2.me/theorems/91ef56e6-6858-47e1-9b0c-25b49890d5fa
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult_outputs: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult_outputs` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoaderCore.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoaderCore.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader`, with `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram`, `open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage`):
--
--   ```lean
--   theorem localResult_outputs (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
--       (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
--       (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
--       let e := localResult a rp rm rs n N W z rows low raw shifted
--       let js := selectedHeads n rows low z
--       e.stacks 650=HeadScatterProgram.indices js ∧
--       e.stacks 651=List.replicate js.length false ∧
--       e.stacks 670=HeadScatterProgram.mask n js (List.replicate js.length true) ∧
--       e.stacks 671=ProgramEncoding.encodeRecords
--         ((LeafHeadFactorsProgram.chosenIds (LeafHeadFactorsProgram.predicate rows n z) N).map
--           Encoding.encodeNat)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.Pair` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.selectedHeads` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.mask` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.chosenIds` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.predicate` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.ProgramEncoding.encodeRecords` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.indices` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.evaluateHead_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.load_run_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result_mask_word`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.load_run_polynomial` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.result_headsize` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoaderCore.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult_outputs)

import Mathlib
import Definitions.Def_SubexponentialSAT
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

theorem localResult_outputs (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    let e := localResult a rp rm rs n N W z rows low raw shifted
    let js := selectedHeads n rows low z
    e.stacks 650=HeadScatterProgram.indices js ∧
    e.stacks 651=List.replicate js.length false ∧
    e.stacks 670=HeadScatterProgram.mask n js (List.replicate js.length true) ∧
    e.stacks 671=ProgramEncoding.encodeRecords
      ((LeafHeadFactorsProgram.chosenIds (LeafHeadFactorsProgram.predicate rows n z) N).map
        Encoding.encodeNat) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end
