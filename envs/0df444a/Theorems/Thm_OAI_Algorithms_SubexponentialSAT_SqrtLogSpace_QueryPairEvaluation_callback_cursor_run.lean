-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation_callback_cursor_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_cursor_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:33:51.982934+00:00
-- url     : https://prove2.me/theorems/f923d66c-c1bb-493f-8d3b-f6c9fb6a4a74
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_cursor_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_cursor_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryPairEvaluation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryPairEvaluation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation`, with `open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing`, `open LeafProgram QueryTupleState QueryPairCommit QueryReadyConstruction`, `open SignatureTupleSource`, `open scoped BigOperators`, `open SqrtLog.ProgramTapeReplay`):
--
--   ```lean
--   theorem callback_cursor_run (s : ProducedSource) {d M F S Z B width height : ℕ}
--       (q : Factor.Spec s.input.r s.input.Q s.input.n d)
--       (H : Finset (Fin s.input.n)) (high : H → Bool)
--       (owner : Fin q.ps.length → Fin s.input.n)
--       (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
--       (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
--       (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
--       (cap : SignatureTupleComplete.RetainedCap s F)
--       (hheads : ∀ depth < s.input.r,s.headSize depth ≤ height)
--       (origin a : State 40 896) (total : Truncated (q.p.model.O q.p.t) q.J)
--       (hi : Invariant q s.input.node H high M F s origin total a)
--       (hm : origin.stacks 338=HighIncidenceProgram.descendingHighMask H)
--       (haddress : origin.stacks 649=List.replicate s.base true)
--       (J : ℕ) (word : List (Option Bool)) (hlen : word.length=s.input.n-H.card)
--       (hc : DifferencePairsProgram.Cursor QueryStreamProgram.pairPorts 0 J word true a) :
--       ∃ steps b,
--         Eval QueryStreamProgram.pairCallback steps
--           (DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 a) b ∧
--         steps ≤ callbackBudget s q (s.input.n-H.card) F S Z B height ∧
--         (∀ j,b.stacks (QueryStreamProgram.pairPorts.stack j)=a.stacks (QueryStreamProgram.pairPorts.stack j)) ∧
--         Invariant q s.input.node H high M F s origin
--           (visit (s.input.n-H.card) (pairValue s q H high owner head facts) word total) b ∧
--         ((∀ i,(a.stacks i).length ≤ F) → (∀ i,(b.stacks i).length ≤ F) ∧
--           QueryExecution.PrefixBound QueryStreamProgram.pairCallback (steps+1)
--             (DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 a)
--             (callbackSpace s q (s.input.n-H.card) F B))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.Ports` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.visit` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram.descendingHighMask` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.Cursor`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.popped` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.pairPorts` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommRing` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.PrefixBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.base` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.headSize` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.Invariant`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callbackSpace`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.SourceFacts` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.RetainedCap` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.pairValue` (definitions bundle `OAIQ081S190` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callbackBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.pairCallback` (definitions bundle `OAIQ081S191` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.HeadBounds` (definitions bundle `OAIQ081S193` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryPairEvaluation.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_cursor_run)

import Mathlib
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram QueryTupleState QueryPairCommit QueryReadyConstruction
open SignatureTupleSource
open scoped BigOperators
open SqrtLog.ProgramTapeReplay

local notation "Hidden" => (fun i : Fin 896 => Fin.val i=832 ∨ Fin.val i=833)

theorem callback_cursor_run (s : ProducedSource) {d M F S Z B width height : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : SignatureTupleComplete.RetainedCap s F)
    (hheads : ∀ depth < s.input.r,s.headSize depth ≤ height)
    (origin a : State 40 896) (total : Truncated (q.p.model.O q.p.t) q.J)
    (hi : Invariant q s.input.node H high M F s origin total a)
    (hm : origin.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (haddress : origin.stacks 649=List.replicate s.base true)
    (J : ℕ) (word : List (Option Bool)) (hlen : word.length=s.input.n-H.card)
    (hc : DifferencePairsProgram.Cursor QueryStreamProgram.pairPorts 0 J word true a) :
    ∃ steps b,
      Eval QueryStreamProgram.pairCallback steps
        (DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 a) b ∧
      steps ≤ callbackBudget s q (s.input.n-H.card) F S Z B height ∧
      (∀ j,b.stacks (QueryStreamProgram.pairPorts.stack j)=a.stacks (QueryStreamProgram.pairPorts.stack j)) ∧
      Invariant q s.input.node H high M F s origin
        (visit (s.input.n-H.card) (pairValue s q H high owner head facts) word total) b ∧
      ((∀ i,(a.stacks i).length ≤ F) → (∀ i,(b.stacks i).length ≤ F) ∧
        QueryExecution.PrefixBound QueryStreamProgram.pairCallback (steps+1)
          (DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 a)
          (callbackSpace s q (s.input.n-H.card) F B)) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation
end
