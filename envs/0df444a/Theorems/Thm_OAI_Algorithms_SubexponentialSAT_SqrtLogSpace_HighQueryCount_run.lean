-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryCount_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:26:05.954789+00:00
-- url     : https://prove2.me/theorems/fe962e52-ce9a-4dd9-a8a3-7d73294402d6
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryCount.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryCount.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount`, with `open OAI BitProgram StructuredCalls SqrtLog LeafProgram`, `open HighQueryAdapter`, `open LeafParametersProgram PreparedSource PreparedBranchCount LeafBranchProgram`, `open HashGreedyProgram.NativeRound`):
--
--   ```lean
--   theorem run (RB RC RD RI RE : ℕ) (hv : q.Valid)
--       (frontBase : Query.Data) (bw : Bank.Words)
--       (hfront : Query.FrontState q k frontBase (HighMarkedFrontend.project front) padding bw)
--       (hready : q.Ready frontBase) (hindex : q.index=Encoding.encodeNat (markIndex q))
--       (source : List (List (SAT.Literal (Fin n))))
--       (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)
--       (hwidth : ∀ clause∈source,clause.length≤k)
--       (A T : ℕ) (hwords : ∀ i,((seeded).stacks i).length≤A)
--       (hvalues : ∀ i,(model).val i≤A) (hAT : A≤T) (hqsize : 3^((model).val 34)≤T) :
--       let hashes := (castRows (congrArg List.length hsource) q.rows).map
--         (fun terms => terms.map (fun term =>
--           (term.2,HashInputProgram.Expansion.originalClause source term.1)))
--       let resources := ProducedQueryResources.ofPacking q k RB RC RD RI RE hg
--         prepared.first prepared.rest
--       let work := CostAssembly.assembledWork k (ProducedQueryResources.ambient q) resources
--       let F := QueryHeadBudgets.compact A
--       let C := QueryStreamCorrect.budget n ((model).val 33) ((model).val 34)
--         ((model).val 21) ((model).val 42) A T work+11*F+16*(n+2)+15
--       let D := max (max F (QueryStreamCorrect.space n ((model).val 33) ((model).val 34)
--         ((model).val 42) A T)) (20*(n+2))
--       ∃ steps final, Eval HighQueryProgram.highLoop steps seeded final ∧
--         steps+1≤2^(H).card*(C+28*(H).card+12)+3 ∧
--         BinaryArithmetic.toNat (final.stacks 788)=
--           fullCount hashes q.mark.isSome (source[markIndex q]?.getD []) ∧
--         (final.stacks 788).length≤n+1 ∧ final.stacks 323=[] ∧ final.stacks 791=[] ∧
--         final.stacks 789=Encoding.encodeList id (List.replicate (H).card [false]) ∧
--         final.stacks 790=[] ∧ final.regs 21=false ∧
--         (∀ i,HashMarkedReturn.kept i=true → final.stacks i=(seeded).stacks i) ∧
--         (∀ i,(final.stacks i).length≤F) ∧
--         Trace (compiled HighQueryProgram.highLoop 789 788) (steps+1)
--           ((seeded).withPC (some (compiled HighQueryProgram.highLoop 789 788).entry))
--           (final.withPC none) ∧
--         StageSpace HighQueryProgram.highLoop (steps+1) seeded (max D (40*((H).card+1)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Resources` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.kept` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.compact` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.castRows` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.Data` (definitions bundle `OAIQ081S038` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.encodedClauses` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.originalClause` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount.fullCount` (definitions bundle `OAIQ081S076` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.project` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.result` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.StageSpace` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Ready` (definitions bundle `OAIQ081S146` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedModel` (definitions bundle `OAIQ081S153` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.initialized` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.highSet` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ambient` (definitions bundle `OAIQ081S171` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.Data` (definitions bundle `OAIQ081S174` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.markIndex` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.FrontState` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ofPacking` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.budget` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.space` (definitions bundle `OAIQ081S183` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.first`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.rest` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.seedRegs` (definitions bundle `OAIQ081S190` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.highLoop` (definitions bundle `OAIQ081S193` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryCount.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run)

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

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount

open OAI BitProgram StructuredCalls SqrtLog LeafProgram
open HighQueryAdapter

section ActualRun

open LeafParametersProgram PreparedSource PreparedBranchCount LeafBranchProgram
open HashGreedyProgram.NativeRound

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
    {front : Data} {padding : Fin 8 → ℕ} {S B cost : ℕ}
    (prepared : HighQuerySetup.PreparedRun q k hg front padding S B cost)

local notation "seeded" => HighCountSeed.initialized
  (HighMarkedFrontend.result front prepared.output) prepared.seedRegs
local notation "model" => Execute.guardedModel (q.input k) padding
local notation "H" => HighMarkedFrontend.highSet q
local notation "n" => BinaryArithmetic.toNat q.ambient

theorem run (RB RC RD RI RE : ℕ) (hv : q.Valid)
    (frontBase : Query.Data) (bw : Bank.Words)
    (hfront : Query.FrontState q k frontBase (HighMarkedFrontend.project front) padding bw)
    (hready : q.Ready frontBase) (hindex : q.index=Encoding.encodeNat (markIndex q))
    (source : List (List (SAT.Literal (Fin n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (hwidth : ∀ clause∈source,clause.length≤k)
    (A T : ℕ) (hwords : ∀ i,((seeded).stacks i).length≤A)
    (hvalues : ∀ i,(model).val i≤A) (hAT : A≤T) (hqsize : 3^((model).val 34)≤T) :
    let hashes := (castRows (congrArg List.length hsource) q.rows).map
      (fun terms => terms.map (fun term =>
        (term.2,HashInputProgram.Expansion.originalClause source term.1)))
    let resources := ProducedQueryResources.ofPacking q k RB RC RD RI RE hg
      prepared.first prepared.rest
    let work := CostAssembly.assembledWork k (ProducedQueryResources.ambient q) resources
    let F := QueryHeadBudgets.compact A
    let C := QueryStreamCorrect.budget n ((model).val 33) ((model).val 34)
      ((model).val 21) ((model).val 42) A T work+11*F+16*(n+2)+15
    let D := max (max F (QueryStreamCorrect.space n ((model).val 33) ((model).val 34)
      ((model).val 42) A T)) (20*(n+2))
    ∃ steps final, Eval HighQueryProgram.highLoop steps seeded final ∧
      steps+1≤2^(H).card*(C+28*(H).card+12)+3 ∧
      BinaryArithmetic.toNat (final.stacks 788)=
        fullCount hashes q.mark.isSome (source[markIndex q]?.getD []) ∧
      (final.stacks 788).length≤n+1 ∧ final.stacks 323=[] ∧ final.stacks 791=[] ∧
      final.stacks 789=Encoding.encodeList id (List.replicate (H).card [false]) ∧
      final.stacks 790=[] ∧ final.regs 21=false ∧
      (∀ i,HashMarkedReturn.kept i=true → final.stacks i=(seeded).stacks i) ∧
      (∀ i,(final.stacks i).length≤F) ∧
      Trace (compiled HighQueryProgram.highLoop 789 788) (steps+1)
        ((seeded).withPC (some (compiled HighQueryProgram.highLoop 789 788).entry))
        (final.withPC none) ∧
      StageSpace HighQueryProgram.highLoop (steps+1) seeded (max D (40*((H).card+1))) := by
  sorry

end ActualRun

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount
end
