-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeHashQueries_marked_replay
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:29:54.583213+00:00
-- url     : https://prove2.me/theorems/996ba5cb-0474-45ac-9195-72bb2a384d0d
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeHashQueries.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeHashQueries.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries`, with `open BitProgram StructuredCalls SqrtLog DisjointReuse`, `open HighFrontendSources HashGreedyCode HashQueryEntry LeafProgram`, `open HashGreedyProgram.NativeRound`, `open LeafParametersProgram HighMarkedFrontend HighQuerySetup ProducedQueryResources`):
--
--   ```lean
--   theorem marked_replay :
--       ∃ steps output,
--         Eval (HighQueryProgram.marked k) steps input output ∧
--         steps+1 ≤ HighQueryCorrect.markedBudget frontCost (S+frontBudget)
--           (Cp*(S+frontBudget+1)^dp) highCost (QueryHeadBudgets.compact A) ∧
--         output.stacks 323 = countWord (literalCount q source hsource) ∧
--         HashMassAdapter.workspace output = HashMassAdapter.workspace input ∧
--         HashMassAdapter.read output = HashMassAdapter.read input ∧
--         RecordPrograms.state HashMassAdapter.recordPorts output false true false
--           (input.stacks 320) [] = output ∧ output.stacks 324 = [] ∧
--         StageSpace (HighQueryProgram.marked k) (steps+1) input
--           (max (HighQueryCorrect.space q S frontCost (S+frontBudget) 0
--             (Cp*(S+frontBudget+1)^dp) highSpace (QueryHeadBudgets.compact A)) frameBound)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.kept`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.markedBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.compact` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.words` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.RecordPrograms.state` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.encodedClauses` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.recordPorts` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.result` (definitions bundle `OAIQ081S067` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.markedInput` (definitions bundle `OAIQ081S077` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.project` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.StageSpace` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.read` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.workspace` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedModel` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.code` (definitions bundle `OAIQ081S153` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.highSet` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ambient` (definitions bundle `OAIQ081S171` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.MarkedEntry` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.markIndex` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ofPacking`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow.erase` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.Data` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.loopBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.loopSpace` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.space` (definitions bundle `OAIQ081S183` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.literalCount` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.SetupRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.first`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.rest`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.SetupRun.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.SetupRun.guard`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.SetupRun.padding` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.SetupRun.prepared` (definitions bundle `OAIQ081S190` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.marked` (definitions bundle `OAIQ081S193` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat`, `OAI.Algorithms.SubexponentialSAT.SAT.Literal` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeHashQueries.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay)

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

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries

open BitProgram StructuredCalls SqrtLog DisjointReuse
open HighFrontendSources HashGreedyCode HashQueryEntry LeafProgram
open HashGreedyProgram.NativeRound

open LeafParametersProgram HighMarkedFrontend HighQuerySetup ProducedQueryResources

section Replay

variable {q : LeafQueryFrontend.Query} {k : ℕ} {input : State 40 896}
  {frontBudget S Cp dp timeCap A : ℕ}

local notation "erased" => HighQueryEntryShadow.erase input

variable (run : NativeHashQuerySetup.SetupRun q k (HighQueryEntryShadow.erase input) (HighMarkedFrontend.command k)
  (Query.markedInput (project (HighQueryEntryShadow.erase input))) frontBudget S 0 Cp dp timeCap A)
  (RB RI frontCost frameBound : ℕ) (staged : State 40 896)
  (entry : MarkedEntry q staged input)
  (hindex : q.index = Encoding.encodeNat (PreparedSource.markIndex q))
  (source : RawCNF (BinaryArithmetic.toNat q.ambient))
  (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)
  (hwidth : ∀ clause ∈ source, clause.length ≤ k)
  (hvalues : ∀ j,
    (Circuit.result Serialization.code (Execute.guardedModel (q.input k) run.padding)).val j ≤ S ∧
    (Execute.guardedModel (q.input k) run.padding).val j ≤ S)
  (hSA : S ≤ A) (hfront : frontBudget ≤ frontCost)
  (hblank : ∀ i, HashMarkedReturn.kept i = false → (i.val < 320 ∨ 324 < i.val) →
    input.stacks i = [])
  (hhidden : ∀ i, i ∈ HighQueryProgram.Carried.words → (input.stacks i).length ≤ frameBound)

local notation "model" => Execute.guardedModel (q.input k) run.padding
local notation "work" => CostAssembly.assembledWork k (ambient q)
  (ofPacking q k RB 1 1 RI 1 run.guard run.prepared.first run.prepared.rest)
local notation "highCost" => HighQueryCorrect.loopBudget (BinaryArithmetic.toNat q.ambient)
  (Finset.card (highSet q)) (Circuit.Model.val model 33) (Circuit.Model.val model 34) (Circuit.Model.val model 21) (Circuit.Model.val model 42) A (A+S+2) work
local notation "highSpace" => HighQueryCorrect.loopSpace (BinaryArithmetic.toNat q.ambient)
  (Finset.card (highSet q)) (Circuit.Model.val model 33) (Circuit.Model.val model 34) (Circuit.Model.val model 42) A (A+S+2)

include entry hindex hwidth hvalues hSA hfront hblank hhidden in
theorem marked_replay :
    ∃ steps output,
      Eval (HighQueryProgram.marked k) steps input output ∧
      steps+1 ≤ HighQueryCorrect.markedBudget frontCost (S+frontBudget)
        (Cp*(S+frontBudget+1)^dp) highCost (QueryHeadBudgets.compact A) ∧
      output.stacks 323 = countWord (literalCount q source hsource) ∧
      HashMassAdapter.workspace output = HashMassAdapter.workspace input ∧
      HashMassAdapter.read output = HashMassAdapter.read input ∧
      RecordPrograms.state HashMassAdapter.recordPorts output false true false
        (input.stacks 320) [] = output ∧ output.stacks 324 = [] ∧
      StageSpace (HighQueryProgram.marked k) (steps+1) input
        (max (HighQueryCorrect.space q S frontCost (S+frontBudget) 0
          (Cp*(S+frontBudget+1)^dp) highSpace (QueryHeadBudgets.compact A)) frameBound) := by
  sorry

end Replay

open NativeQueryInputBounds Statement

attribute [local irreducible] Execute.guardedModel

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries
end
