-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryCorrect_accepted
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:24:37.76199+00:00
-- url     : https://prove2.me/theorems/c1857451-d62f-4cb2-b7d6-52521db6cdff
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryCorrect.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryCorrect.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect`, with `open BitProgram StructuredCalls HighMarkedFrontend HighQuerySetup`, `open HashGreedyProgram.NativeRound`, `open SqrtLog LeafParametersProgram LeafProgram PreparedSource PreparedBranchCount`):
--
--   ```lean
--   theorem accepted (input : Data) (frontSteps frontCost inputCap : ℕ)
--       (hfront : Eval (HighMarkedFrontend.acceptedCommand k) frontSteps input front)
--       (hfrontCost : frontSteps  ≤  frontCost) (hinput : ∀ i,(input.stacks i).length ≤ inputCap)
--       (hkept : ∀ i,HashMarkedReturn.kept i= true → (seeded).stacks i=input.stacks i)
--       (hblank : ∀ i,i ≠ 788 → HashMarkedReturn.kept i= false → input.stacks i=[])
--       (hscratch : input.stacks 767=[]) :
--       ∃ steps output,
--         Eval (HighQueryProgram.accepted k) steps input output ∧
--         steps+1 ≤ acceptedBudget frontCost S cost highCost (QueryHeadBudgets.compact A) ∧
--         output.stacks=Function.update input.stacks 788 (countWord count) ∧
--         StageSpace (HighQueryProgram.accepted k) (steps+1) input
--           (space q inputCap frontCost S B cost highSpace (QueryHeadBudgets.compact A))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.kept`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.acceptedBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.compact` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.castRows` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.Data` (definitions bundle `OAIQ081S038` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SparseRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.encodedClauses` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.originalClause` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount.fullCount` (definitions bundle `OAIQ081S076` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.project` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.result` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.StageSpace` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Ready` (definitions bundle `OAIQ081S146` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedModel` (definitions bundle `OAIQ081S153` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.initialized` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.highSet` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ambient` (definitions bundle `OAIQ081S171` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.markIndex` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.FrontState` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.Data` (definitions bundle `OAIQ081S176` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ofPacking` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.acceptedCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.loopBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.loopSpace` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.space` (definitions bundle `OAIQ081S183` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.first`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.rest` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.seedRegs` (definitions bundle `OAIQ081S190` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.accepted` (definitions bundle `OAIQ081S193` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat`, `OAI.Algorithms.SubexponentialSAT.SAT.Literal` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryCorrect.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect

open BitProgram StructuredCalls HighMarkedFrontend HighQuerySetup
open HashGreedyProgram.NativeRound

section Complete

open SqrtLog LeafParametersProgram LeafProgram PreparedSource PreparedBranchCount

attribute [local irreducible] Execute.guardedModel

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
  {front : Data} {padding : Fin 8 → ℕ} {S B cost : ℕ}
  (run : PreparedRun q k hg front padding S B cost)

local notation "seeded" => HighCountSeed.initialized (result front run.output) run.seedRegs
local notation "model" => Execute.guardedModel (q.input k) padding
local notation "n" => BinaryArithmetic.toNat q.ambient

variable (RB RC RD RI RE : ℕ) (hv : q.Valid)
  (frontBase : Query.Data) (bw : Bank.Words)
  (hfrontState : Query.FrontState q k frontBase (project front) padding bw)
  (hready : q.Ready frontBase) (hindex : q.index=Encoding.encodeNat (markIndex q))
  (source : List (List (SAT.Literal (Fin (BinaryArithmetic.toNat q.ambient)))))
  (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)
  (hwidth : ∀ clause∈source,clause.length ≤ k)
  (A T : ℕ)
  (hwords : ∀ i,((HighCountSeed.initialized (result front run.output) run.seedRegs).stacks i).length ≤ A)
  (hvalues : ∀ i,(Execute.guardedModel (q.input k) padding).val i ≤ A)
  (hAT : A ≤ T) (hqsize : 3^((Execute.guardedModel (q.input k) padding).val 34) ≤ T)

local notation "hashes" => List.map
  (fun terms => List.map (fun term =>
    (Prod.snd term,HashInputProgram.Expansion.originalClause source (Prod.fst term))) terms)
  (castRows (congrArg List.length hsource) (LeafQueryFrontend.Query.rows q))
local notation "count" => fullCount hashes (Option.isSome (LeafQueryFrontend.Query.mark q))
  (List.getD source (markIndex q) [])
local notation "work" => CostAssembly.assembledWork k (ProducedQueryResources.ambient q)
  (ProducedQueryResources.ofPacking q k RB RC RD RI RE hg run.first run.rest)
local notation "highCost" => loopBudget n (Finset.card (highSet q)) (Circuit.Model.val model 33)
  (Circuit.Model.val model 34) (Circuit.Model.val model 21) (Circuit.Model.val model 42) A T work
local notation "highSpace" => loopSpace n (Finset.card (highSet q)) (Circuit.Model.val model 33)
  (Circuit.Model.val model 34) (Circuit.Model.val model 42) A T

include hv hfrontState hready hindex hwidth hwords hvalues hAT hqsize in
theorem accepted (input : Data) (frontSteps frontCost inputCap : ℕ)
    (hfront : Eval (HighMarkedFrontend.acceptedCommand k) frontSteps input front)
    (hfrontCost : frontSteps  ≤  frontCost) (hinput : ∀ i,(input.stacks i).length ≤ inputCap)
    (hkept : ∀ i,HashMarkedReturn.kept i= true → (seeded).stacks i=input.stacks i)
    (hblank : ∀ i,i ≠ 788 → HashMarkedReturn.kept i= false → input.stacks i=[])
    (hscratch : input.stacks 767=[]) :
    ∃ steps output,
      Eval (HighQueryProgram.accepted k) steps input output ∧
      steps+1 ≤ acceptedBudget frontCost S cost highCost (QueryHeadBudgets.compact A) ∧
      output.stacks=Function.update input.stacks 788 (countWord count) ∧
      StageSpace (HighQueryProgram.accepted k) (steps+1) input
        (space q inputCap frontCost S B cost highSpace (QueryHeadBudgets.compact A)) := by
  sorry

end Complete
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect
end
