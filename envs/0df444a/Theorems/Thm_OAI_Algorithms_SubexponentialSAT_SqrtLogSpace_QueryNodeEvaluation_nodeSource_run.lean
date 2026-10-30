-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation_nodeSource_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:32:52.450081+00:00
-- url     : https://prove2.me/theorems/74f97d2f-c5ca-4a35-ac35-4dadb6d2516b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeEvaluation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeEvaluation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation`, with `open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage`, `open LeafHeadSetupProgram QueryTupleState`, `open LeafParametersProgram LeafProgram LeafProgram.PreparedSource`, `open SubexpLiftRing SubexpQuarticRing`, `open scoped BigOperators`):
--
--   ```lean
--   theorem nodeSource_run (high : H → Bool) (F S Z T width height : ℕ)
--       (caps : QueryVisitorHead.HeadBounds (src).input spec A F S Z T A width)
--       (cap : SignatureTupleComplete.RetainedCap src F)
--       (hheads : ∀ depth<(native).r,(src).headSize depth ≤ height)
--       (b : Data) (np : ℕ) (hp : Eval prepareNode np a b)
--       (ha : WordBound F a) (hb : WordBound F b)
--       (hcommon : QueryReadyConstruction.CommonReady spec node H high A b)
--       (hzero : QueryPairCommit.NodeAccumulatorMeaning spec 0 b)
--       (hmasters : SignatureHeadLoader.MasterFrame
--         (Native.start native (sourceSnapshot a bits remaining) ra rd rc words)
--         (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b))
--       (hframe : ∀ i ∈ framePorts,b.stacks i=a.stacks i)
--       (hmask : b.stacks 338=HighIncidenceProgram.descendingHighMask H)
--       (haddress : b.stacks 649=unary (src).base)
--       (hdepth : b.stacks 832=List.replicate ((native).n-(H).card) true)
--       (hbudget : b.stacks 833=List.replicate (spec).J true)
--       (houter : b.stacks 834=[]) (hinner : b.stacks 835=[])
--       (hcursor : b.stacks 301=Encoding.encodeList id remaining)
--       (hout : (b.stacks 863).length+(spec).J*((m.val 34)*baseWidth 3 (spec).p.t) ≤ F)
--       (hnext : node.val+1 ≤ F) :
--       ∃ steps z, ∃ codes : List (RingProgram.Code (Word (baseWidth 3 (spec).p.t)) (m.val 34)),
--         Eval QueryStreamProgram.nodeBody steps a z ∧
--         codes.length=(spec).J ∧
--         codes.map (spec).p.ops.decode=List.ofFn
--           (Truncated.ofPolynomial (spec).J ((NodeConcrete.specTarget spec H high).comp
--             (Polynomial.X+Polynomial.C ((spec).p.ops.decode (spec).theta)))).coeff ∧
--         z.stacks 863=a.stacks 863++(codes.map RingProgram.flat).flatten ∧
--         z.stacks 301=Encoding.encodeList id remaining ∧
--         z.stacks 307=List.replicate (node.val+1) true ∧
--         z.regs 37= !remaining.isEmpty ∧ z.regs 38=true ∧ z.stacks 89=[] ∧
--         (∀ i ∈ framePorts,i ≠ 307 → i ≠ 863 → z.stacks i=a.stacks i) ∧
--         WordBound F z ∧
--         steps ≤ np+DifferencePairsProgram.cost
--           (QueryPairEvaluation.callbackBudget src spec ((native).n-(H).card) F S Z T height)
--           ((native).n-(H).card) (spec).J+
--           QueryNodeFinish.budget (native).n (baseWidth 3 (spec).p.t) (m.val 34) (spec).p.t (spec).J F ∧
--         Trace (compiled QueryStreamProgram.nodeBody 838 838) (steps+1)
--           (a.withPC (some (compiled QueryStreamProgram.nodeBody 838 838).entry)) (z.withPC none) ∧
--         QueryExecution.PrefixBound QueryStreamProgram.nodeBody (steps+1) a
--           (max (max (QueryPairEvaluation.callbackSpace src spec ((native).n-(H).card) F T) (896*F+13))
--             (896*F+np+QueryNodeFinish.budget (native).n (baseWidth 3 (spec).p.t)
--               (m.val 34) (spec).p.t (spec).J F+1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` and `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters.high` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.cost` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instZero` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad.stackMap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.framePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.leafRegs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.lowStacks` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Data` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram.descendingHighMask` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.encodedClauses` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.CacheCorrect` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.budget` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.ofPolynomial` (definitions bundle `OAIQ081S080` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.MasterFrame` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ops` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.highSet` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad.SourceBank` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Produced` (definitions bundle `OAIQ081S166` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.start`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.packingProblem` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepareNode` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.queryInputsAddressed` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.PrefixBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit.NodeAccumulatorMeaning`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.base`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.headSize` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.specTarget` (definitions bundle `OAIQ081S181` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.sourceSnapshot`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callbackSpace`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction.CommonReady` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.RetainedCap` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction.sourceSpec` (definitions bundle `OAIQ081S188` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callbackBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.nodeBody` (definitions bundle `OAIQ081S191` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.HeadBounds` (definitions bundle `OAIQ081S193` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.node_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeEvaluation.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_run)

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

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram QueryTupleState

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators

section AddressedSource
variable (query : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (query.input k))
  (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q)
  (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem query k hg).Q)
local notation "native" => Native.queryInputsAddressed query k hg first tail node
variable (a : Data) (bits : List Bool) (remaining : List (List Bool)) (A : ℕ)
  (hbank : NativeLayoutLoad.SourceBank (Native.queryInputsAddressed query k hg first tail node) a)
  (hparked : ∀ j : Fin 14,
    (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length ≤ A)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed query k hg first tail node).height
    (unary (Native.queryInputsAddressed query k hg first tail node).R)
    (Native.queryInputsAddressed query k hg first tail node).width words)

local notation "src" => nodeSource query k hg first tail node a bits remaining A hbank hparked ra rd rc words hc

section FactorRun
variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
  (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
  (cache : RingProgram.ScalarCache 3 (m.val 33))
  (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
  (produced : LeafRingSetupProgram.Produced m hd M cache half e)
  (hfield : (Native.queryInputsAddressed query k hg first tail node).Q < 3^(m.val 34)) (hv : query.Valid) (hJ : 0 < m.val 42)
  (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed query k hg first tail node).n))))
  (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source)
local notation "spec" => QueryReadyConstruction.sourceSpec src m ht hd M cache half e produced
  hfield query hv hJ source hsource
local notation "H" => HighMarkedFrontend.highSet query
local notation "sourceOwner" => ProducedQueryRank.owner (LeafProgram.Query.packingProblem query k hg) ∘
  Fin.cast (Native.Inputs.plans_length native)
local notation "sourceHead" => (fun t v => ProducedQueryRank.words
  (LeafProgram.Query.packingProblem query k hg) first tail (Sum.inl v) t)
local notation "sourceFacts" => nodeSource_facts query k hg first tail node a bits remaining A
  hbank hparked ra rd rc words hc m ht hd M cache half e produced hfield hv hJ source hsource

include hfield source hsource in
theorem nodeSource_run (high : H → Bool) (F S Z T width height : ℕ)
    (caps : QueryVisitorHead.HeadBounds (src).input spec A F S Z T A width)
    (cap : SignatureTupleComplete.RetainedCap src F)
    (hheads : ∀ depth<(native).r,(src).headSize depth ≤ height)
    (b : Data) (np : ℕ) (hp : Eval prepareNode np a b)
    (ha : WordBound F a) (hb : WordBound F b)
    (hcommon : QueryReadyConstruction.CommonReady spec node H high A b)
    (hzero : QueryPairCommit.NodeAccumulatorMeaning spec 0 b)
    (hmasters : SignatureHeadLoader.MasterFrame
      (Native.start native (sourceSnapshot a bits remaining) ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b))
    (hframe : ∀ i ∈ framePorts,b.stacks i=a.stacks i)
    (hmask : b.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (haddress : b.stacks 649=unary (src).base)
    (hdepth : b.stacks 832=List.replicate ((native).n-(H).card) true)
    (hbudget : b.stacks 833=List.replicate (spec).J true)
    (houter : b.stacks 834=[]) (hinner : b.stacks 835=[])
    (hcursor : b.stacks 301=Encoding.encodeList id remaining)
    (hout : (b.stacks 863).length+(spec).J*((m.val 34)*baseWidth 3 (spec).p.t) ≤ F)
    (hnext : node.val+1 ≤ F) :
    ∃ steps z, ∃ codes : List (RingProgram.Code (Word (baseWidth 3 (spec).p.t)) (m.val 34)),
      Eval QueryStreamProgram.nodeBody steps a z ∧
      codes.length=(spec).J ∧
      codes.map (spec).p.ops.decode=List.ofFn
        (Truncated.ofPolynomial (spec).J ((NodeConcrete.specTarget spec H high).comp
          (Polynomial.X+Polynomial.C ((spec).p.ops.decode (spec).theta)))).coeff ∧
      z.stacks 863=a.stacks 863++(codes.map RingProgram.flat).flatten ∧
      z.stacks 301=Encoding.encodeList id remaining ∧
      z.stacks 307=List.replicate (node.val+1) true ∧
      z.regs 37= !remaining.isEmpty ∧ z.regs 38=true ∧ z.stacks 89=[] ∧
      (∀ i ∈ framePorts,i ≠ 307 → i ≠ 863 → z.stacks i=a.stacks i) ∧
      WordBound F z ∧
      steps ≤ np+DifferencePairsProgram.cost
        (QueryPairEvaluation.callbackBudget src spec ((native).n-(H).card) F S Z T height)
        ((native).n-(H).card) (spec).J+
        QueryNodeFinish.budget (native).n (baseWidth 3 (spec).p.t) (m.val 34) (spec).p.t (spec).J F ∧
      Trace (compiled QueryStreamProgram.nodeBody 838 838) (steps+1)
        (a.withPC (some (compiled QueryStreamProgram.nodeBody 838 838).entry)) (z.withPC none) ∧
      QueryExecution.PrefixBound QueryStreamProgram.nodeBody (steps+1) a
        (max (max (QueryPairEvaluation.callbackSpace src spec ((native).n-(H).card) F T) (896*F+13))
          (896*F+np+QueryNodeFinish.budget (native).n (baseWidth 3 (spec).p.t)
            (m.val 34) (spec).p.t (spec).J F+1)) := by
  sorry

end FactorRun

end AddressedSource

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end
