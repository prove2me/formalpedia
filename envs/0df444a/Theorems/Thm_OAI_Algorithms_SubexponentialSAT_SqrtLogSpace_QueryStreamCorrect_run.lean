-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:35:19.648986+00:00
-- url     : https://prove2.me/theorems/05aa81ec-7f39-41fc-a39a-84281caf9411
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamCorrect.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamCorrect.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect`, with `open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing`, `open SubexpSetupStorage`, `open LeafParametersProgram LeafProgram LeafProgram.PreparedSource LeafHeadSetupProgram`, `open QueryNodeEvaluation`):
--
--   ```lean
--   theorem run (A S : ℕ) (a : State 40 896)
--       (frontBase front : State 40 768) (bw : Bank.Words)
--       (hf : Query.FrontState query k frontBase front padding bw)
--       (hpark : ∀ j : Fin 14,
--         a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j)) =
--           (PackingCallerProgram.result front (Query.packingProblem query k hg)
--             first tail).stacks (LayoutMasters.high j))
--       (hparked : ∀ j : Fin 14,
--         (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length≤A)
--       (hcache : ∀ i∈cacheInputPorts,(a.stacks i).length≤A)
--       (hvalues : ∀ i,m.val i≤A)
--       (hsources : Query.Sources query (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort a))
--       (h700 : (a.stacks 700).length≤A) (h701 : (a.stacks 701).length≤A)
--       (h708 : (a.stacks 708).length≤A)
--       (hnodes : a.stacks 300=Encoding.encodeList id
--         (RingNodeMetadata.nodeBits (m.val 33) (m.val 34) (m.val 21)))
--       (hmask : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
--       (hframe : ∀ i∈QueryReadyConstruction.arithmeticPorts,a.stacks (i.castAdd 128)=out.stacks i)
--       (hdegree : out.stacks 204=List.replicate (m.val 34) true)
--       (h704 : a.stacks 704=List.replicate query.rows.length true)
--       (h705 : a.stacks 705=Encoding.encodeNat (markIndex query))
--       (h706 : a.stacks 706=[query.mark.isSome])
--       (counterWords : List (List Bool))
--       (hshape : counterWords.map List.length=List.replicate (H).card 1)
--       (rank : Fin (2^(H).card)) (hrank : CounterPrograms.value counterWords.flatten=rank.val)
--       (hcounter : a.stacks 330=Encoding.encodeList id counterWords)
--       (hring : ∀ i∈QueryReconstruction.ringPorts,
--         a.stacks (i.castAdd 576)=e.stacks (i.castAdd 320))
--       (hflat : a.stacks 256=e.stacks 256)
--       (hwidth : ∀ clause∈source,clause.length≤k)
--       (ha : WordBound (QueryHeadBudgets.compact A) a)
--       (hAS : A≤S) (hqsize : 3^(m.val 34)≤S)
--       (hmodsize : (a.stacks 194).length≤S) (hwidthsize : (a.stacks 202).length≤S)
--       (hambient : (native).n+1≤QueryHeadBudgets.compact A) :
--       ∃ words, ∃ hc : CacheCorrect (native).height (unary (native).R) (native).width words,
--       ∃ steps final,
--         let high := HighIncidenceProgram.Rank.highEquiv (HighIncidenceProgram.Order.highOrder H) rank
--         let factor := nativeSpecOfInputs native m ht hd words hc M cache half e ho.produced
--           hfield query hv (m.val 42) hJ source hsource
--         Eval QueryStreamProgram.command steps a final ∧
--         Trace QueryStreamProgram.program (steps+1)
--           (a.withPC (some QueryStreamProgram.program.entry)) (final.withPC none) ∧
--         final.stacks 323=DisjointReuse.binaryNat
--           (NodeSemantics.ternaryFixedHighCount H high (NodeConcrete.sourceHashes factor)
--             factor.marked factor.markedClause) ∧
--         final.stacks 863=[] ∧ WordBound (QueryHeadBudgets.compact A) final ∧
--         (∀ i∈retainedPorts,i≠702 → i≠703 → final.stacks i=a.stacks i) ∧
--         (∀ i,HashMarkedReturn.kept i=true → final.stacks i=a.stacks i) ∧
--         steps+1≤budget (native).n (m.val 33) (m.val 34) (m.val 21) (m.val 42) A S work ∧
--         QueryExecution.PrefixBound QueryStreamProgram.command (steps+1) a
--           (space (native).n (m.val 33) (m.val 34) (m.val 42) A S)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.highOrder` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters.high` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.binaryNat` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.kept`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad.stackMap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.compact`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.cacheInputPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction.arithmeticPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.ringPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.retainedPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.Nodes.lowPort` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Data` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram.descendingHighMask` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.encodedClauses` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.CacheCorrect` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.ternaryFixedHighCount` (definitions bundle `OAIQ081S076` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank.highEquiv` (definitions bundle `OAIQ081S102` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.Sources` (definitions bundle `OAIQ081S146` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedModel` (definitions bundle `OAIQ081S153` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.highSet` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata.nodeBits` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.packingProblem` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.sourceHashes` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.markedClause` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ambient` (definitions bundle `OAIQ081S171` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.queryInputsAddressed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.markIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.ArithmeticOutput` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.FrontState` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.result` (definitions bundle `OAIQ081S176` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ofPacking` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.PrefixBound` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.nativeSpecOfInputs` (definitions bundle `OAIQ081S181` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.budget` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.space` (definitions bundle `OAIQ081S183` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.program` (definitions bundle `OAIQ081S193` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamCorrect.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.run)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open SubexpSetupStorage

section ActualNode
open LeafParametersProgram LeafProgram LeafProgram.PreparedSource LeafHeadSetupProgram
open QueryNodeEvaluation

variable (query : LeafQueryFrontend.Query) (k RB RC RD RI RE : ℕ)
  (hg : Guard (query.input k)) (hv : query.Valid)
  (first : MulticolorTypes.Word (Query.packingProblem query k hg).r
    (Query.packingProblem query k hg).Q)
  (tail : List (MulticolorTypes.Word (Query.packingProblem query k hg).r
    (Query.packingProblem query k hg).Q))
  (node : Fin (Query.packingProblem query k hg).Q)
  (m : Circuit.Model) (padding : Fin 8 → ℕ)
  (hm : m=Execute.guardedModel (query.input k) padding)
  (ht : 0 < m.val 33) (hd : 0 < m.val 34)
  (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
  (cache : RingProgram.ScalarCache 3 (m.val 33))
  (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
  (base out : State 40 768) (ho : Query.ArithmeticOutput base out m hd M cache half e)
  (hfield : (Native.queryInputsAddressed query k hg first tail node).Q < 3 ^ (m.val 34))
  (hQ : m.val 21=(Native.queryInputsAddressed query k hg first tail node).Q)
  (hR : (base.stacks 740).length=(Native.queryInputsAddressed query k hg first tail node).R)
  (hJ : 0 < m.val 42)
  (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed query k hg first tail node).n))))
  (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source)
local notation "native" => Native.queryInputsAddressed query k hg first tail node
local notation "H" => HighMarkedFrontend.highSet query
local notation "resources" => ProducedQueryResources.ofPacking query k RB RC RD RI RE hg first tail
local notation "work" => CostAssembly.assembledWork k (ProducedQueryResources.ambient query) resources

include hm hQ hR in
theorem run (A S : ℕ) (a : State 40 896)
    (frontBase front : State 40 768) (bw : Bank.Words)
    (hf : Query.FrontState query k frontBase front padding bw)
    (hpark : ∀ j : Fin 14,
      a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j)) =
        (PackingCallerProgram.result front (Query.packingProblem query k hg)
          first tail).stacks (LayoutMasters.high j))
    (hparked : ∀ j : Fin 14,
      (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length≤A)
    (hcache : ∀ i∈cacheInputPorts,(a.stacks i).length≤A)
    (hvalues : ∀ i,m.val i≤A)
    (hsources : Query.Sources query (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort a))
    (h700 : (a.stacks 700).length≤A) (h701 : (a.stacks 701).length≤A)
    (h708 : (a.stacks 708).length≤A)
    (hnodes : a.stacks 300=Encoding.encodeList id
      (RingNodeMetadata.nodeBits (m.val 33) (m.val 34) (m.val 21)))
    (hmask : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (hframe : ∀ i∈QueryReadyConstruction.arithmeticPorts,a.stacks (i.castAdd 128)=out.stacks i)
    (hdegree : out.stacks 204=List.replicate (m.val 34) true)
    (h704 : a.stacks 704=List.replicate query.rows.length true)
    (h705 : a.stacks 705=Encoding.encodeNat (markIndex query))
    (h706 : a.stacks 706=[query.mark.isSome])
    (counterWords : List (List Bool))
    (hshape : counterWords.map List.length=List.replicate (H).card 1)
    (rank : Fin (2^(H).card)) (hrank : CounterPrograms.value counterWords.flatten=rank.val)
    (hcounter : a.stacks 330=Encoding.encodeList id counterWords)
    (hring : ∀ i∈QueryReconstruction.ringPorts,
      a.stacks (i.castAdd 576)=e.stacks (i.castAdd 320))
    (hflat : a.stacks 256=e.stacks 256)
    (hwidth : ∀ clause∈source,clause.length≤k)
    (ha : WordBound (QueryHeadBudgets.compact A) a)
    (hAS : A≤S) (hqsize : 3^(m.val 34)≤S)
    (hmodsize : (a.stacks 194).length≤S) (hwidthsize : (a.stacks 202).length≤S)
    (hambient : (native).n+1≤QueryHeadBudgets.compact A) :
    ∃ words, ∃ hc : CacheCorrect (native).height (unary (native).R) (native).width words,
    ∃ steps final,
      let high := HighIncidenceProgram.Rank.highEquiv (HighIncidenceProgram.Order.highOrder H) rank
      let factor := nativeSpecOfInputs native m ht hd words hc M cache half e ho.produced
        hfield query hv (m.val 42) hJ source hsource
      Eval QueryStreamProgram.command steps a final ∧
      Trace QueryStreamProgram.program (steps+1)
        (a.withPC (some QueryStreamProgram.program.entry)) (final.withPC none) ∧
      final.stacks 323=DisjointReuse.binaryNat
        (NodeSemantics.ternaryFixedHighCount H high (NodeConcrete.sourceHashes factor)
          factor.marked factor.markedClause) ∧
      final.stacks 863=[] ∧ WordBound (QueryHeadBudgets.compact A) final ∧
      (∀ i∈retainedPorts,i≠702 → i≠703 → final.stacks i=a.stacks i) ∧
      (∀ i,HashMarkedReturn.kept i=true → final.stacks i=a.stacks i) ∧
      steps+1≤budget (native).n (m.val 33) (m.val 34) (m.val 21) (m.val 42) A S work ∧
      QueryExecution.PrefixBound QueryStreamProgram.command (steps+1) a
        (space (native).n (m.val 33) (m.val 34) (m.val 42) A S) := by
  sorry

end ActualNode

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect
end
