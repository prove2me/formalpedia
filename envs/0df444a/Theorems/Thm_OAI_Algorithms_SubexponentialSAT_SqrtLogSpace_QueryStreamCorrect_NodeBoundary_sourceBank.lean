-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect_NodeBoundary_sourceBank
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.NodeBoundary.sourceBank
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:19:19.791303+00:00
-- url     : https://prove2.me/theorems/22344f8b-059b-4bfc-80d1-5a548b269895
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.NodeBoundary.sourceBank: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.NodeBoundary.sourceBank` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamCorrect.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamCorrect.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect`, with `open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing`, `open SubexpSetupStorage`):
--
--   ```lean
--   theorem NodeBoundary.sourceBank
--       (query : LeafQueryFrontend.Query) (k : ℕ)
--       (hg : LeafParametersProgram.Guard (query.input k))
--       (base front : State 40 768) (lengths : Fin 8 → ℕ)
--       (bw : LeafParametersProgram.Bank.Words)
--       (hf : LeafProgram.Query.FrontState query k base front lengths bw)
--       (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
--         (LeafProgram.Query.packingProblem query k hg).Q)
--       (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
--         (LeafProgram.Query.packingProblem query k hg).Q))
--       (node : Fin (LeafProgram.Query.packingProblem query k hg).Q)
--       {initial a : Data} {t d Q J B : ℕ}
--       (h : NodeBoundary initial t d Q J B node.val a)
--       (hpark : ∀ i : Fin 14,
--         initial.stacks (NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i)) =
--           (PackingCallerProgram.result front (LeafProgram.Query.packingProblem query k hg)
--             first tail).stacks (LeafProgram.LayoutMasters.high i)) :
--       NativeLayoutLoad.SourceBank
--         (LeafHeadSetupProgram.Native.queryInputsAddressed query k hg first tail node) a
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters.high` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad.stackMap` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad.SourceBank` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.packingProblem` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.queryInputsAddressed` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.FrontState` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.result` (definitions bundle `OAIQ081S176` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.NodeBoundary` (definitions bundle `OAIQ081S178` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.nodes_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamCorrect.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.NodeBoundary.sourceBank)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S175
import Definitions.Def_OAIQ081S176
import Definitions.Def_OAIQ081S178

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open SubexpSetupStorage

theorem NodeBoundary.sourceBank
    (query : LeafQueryFrontend.Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (query.input k))
    (base front : State 40 768) (lengths : Fin 8 → ℕ)
    (bw : LeafParametersProgram.Bank.Words)
    (hf : LeafProgram.Query.FrontState query k base front lengths bw)
    (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
      (LeafProgram.Query.packingProblem query k hg).Q)
    (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
      (LeafProgram.Query.packingProblem query k hg).Q))
    (node : Fin (LeafProgram.Query.packingProblem query k hg).Q)
    {initial a : Data} {t d Q J B : ℕ}
    (h : NodeBoundary initial t d Q J B node.val a)
    (hpark : ∀ i : Fin 14,
      initial.stacks (NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i)) =
        (PackingCallerProgram.result front (LeafProgram.Query.packingProblem query k hg)
          first tail).stacks (LeafProgram.LayoutMasters.high i)) :
    NativeLayoutLoad.SourceBank
      (LeafHeadSetupProgram.Native.queryInputsAddressed query k hg first tail node) a := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect
end
