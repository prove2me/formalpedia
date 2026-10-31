-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect_nodes_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.nodes_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:14:00.26023+00:00
-- url     : https://prove2.me/theorems/1483cffb-3841-4541-bdba-a55ed09082d0
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.nodes_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.nodes_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamCorrect.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamCorrect.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect`, with `open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing`, `open SubexpSetupStorage`, `open LeafParametersProgram LeafProgram LeafProgram.PreparedSource LeafHeadSetupProgram`, `open QueryNodeEvaluation`):
--
--   ```lean
--   theorem nodes_run (high : H → Bool) (A : ℕ) (a : State 40 896)
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
--       (h702 : a.stacks 702=List.ofFn
--         (fun v : Fin (BinaryArithmetic.toNat query.ambient) => decide (v ∈ H)))
--       (h703 : a.stacks 703=List.ofFn
--         (fun v : Fin (BinaryArithmetic.toNat query.ambient) =>
--           if h : v ∈ H then high ⟨v, h⟩ else false))
--       (ha : WordBound (QueryHeadBudgets.compact A) a)
--       (model_eq : m = Execute.guardedModel (query.input k) padding)
--       (query_count : m.val 21 = (native).Q)
--       (radius_eq : (base.stacks 740).length = (native).R) :
--       ∃ words, ∃ hc : CacheCorrect (native).height (unary (native).R) (native).width words,
--       ∃ (steps : ℕ) (z : Data) (outputs : List (List Bool)),
--         let factor := nativeSpecOfInputs native m ht hd words hc M cache half e ho.produced
--           hfield query hv (m.val 42) hJ source hsource
--         Eval QueryStreamProgram.nodes steps a z ∧
--         NodeBoundary a (m.val 33) (m.val 34) (m.val 21) (m.val 42)
--           (QueryHeadBudgets.compact A) (m.val 21) z ∧
--         outputs.length=m.val 21 ∧ z.stacks 863=outputs.flatten ∧
--         (∀ i (hi : i<outputs.length),
--           ∃ codes : List (DensePolynomialProgram.Coeff (baseWidth 3 (m.val 33)) (m.val 34)),
--             codes.length=m.val 42 ∧
--             codes.map factor.p.ops.decode=List.ofFn
--               (Truncated.ofPolynomial (m.val 42) ((NodeConcrete.specTarget factor H high).comp
--                 (Polynomial.X+Polynomial.C (factor.p.ops.decode
--                   (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i+1)))))).coeff ∧
--             outputs[i]'hi=(codes.map RingProgram.flat).flatten) ∧
--         steps≤23*QueryHeadBudgets.compact A+
--           (m.val 21)*(nodeBudget (native).n (m.val 33) (m.val 34) (m.val 42) A work+1)+32 ∧
--         QueryExecution.PrefixBound QueryStreamProgram.nodes (steps+1) a
--           (max (919*QueryHeadBudgets.compact A+31)
--             (nodeSpace (native).n (m.val 33) (m.val 34) (m.val 42) A))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` and `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters.high` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad.stackMap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.compact`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.cacheInputPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction.arithmeticPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.Nodes.lowPort` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Data` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram.descendingHighMask` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.encodedClauses` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.CacheCorrect` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.ofPolynomial` (definitions bundle `OAIQ081S080` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgram.nodeCode` (definitions bundle `OAIQ081S122` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.Sources` (definitions bundle `OAIQ081S146` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedModel` (definitions bundle `OAIQ081S153` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ops` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.highSet` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata.nodeBits` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.packingProblem` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ambient` (definitions bundle `OAIQ081S171` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.queryInputsAddressed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.markIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.ArithmeticOutput` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.FrontState` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.result` (definitions bundle `OAIQ081S176` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.nodeSpace` (definitions bundle `OAIQ081S177` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ofPacking`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.PrefixBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.NodeBoundary` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.specTarget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.nativeSpecOfInputs` (definitions bundle `OAIQ081S181` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.nodeBudget` (definitions bundle `OAIQ081S183` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.nodes` (definitions bundle `OAIQ081S191` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamCorrect.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.nodes_run)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191

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

omit hm hQ hR in
theorem nodes_run (high : H → Bool) (A : ℕ) (a : State 40 896)
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
    (h702 : a.stacks 702=List.ofFn
      (fun v : Fin (BinaryArithmetic.toNat query.ambient) => decide (v ∈ H)))
    (h703 : a.stacks 703=List.ofFn
      (fun v : Fin (BinaryArithmetic.toNat query.ambient) =>
        if h : v ∈ H then high ⟨v, h⟩ else false))
    (ha : WordBound (QueryHeadBudgets.compact A) a)
    (model_eq : m = Execute.guardedModel (query.input k) padding)
    (query_count : m.val 21 = (native).Q)
    (radius_eq : (base.stacks 740).length = (native).R) :
    ∃ words, ∃ hc : CacheCorrect (native).height (unary (native).R) (native).width words,
    ∃ (steps : ℕ) (z : Data) (outputs : List (List Bool)),
      let factor := nativeSpecOfInputs native m ht hd words hc M cache half e ho.produced
        hfield query hv (m.val 42) hJ source hsource
      Eval QueryStreamProgram.nodes steps a z ∧
      NodeBoundary a (m.val 33) (m.val 34) (m.val 21) (m.val 42)
        (QueryHeadBudgets.compact A) (m.val 21) z ∧
      outputs.length=m.val 21 ∧ z.stacks 863=outputs.flatten ∧
      (∀ i (hi : i<outputs.length),
        ∃ codes : List (DensePolynomialProgram.Coeff (baseWidth 3 (m.val 33)) (m.val 34)),
          codes.length=m.val 42 ∧
          codes.map factor.p.ops.decode=List.ofFn
            (Truncated.ofPolynomial (m.val 42) ((NodeConcrete.specTarget factor H high).comp
              (Polynomial.X+Polynomial.C (factor.p.ops.decode
                (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i+1)))))).coeff ∧
          outputs[i]'hi=(codes.map RingProgram.flat).flatten) ∧
      steps≤23*QueryHeadBudgets.compact A+
        (m.val 21)*(nodeBudget (native).n (m.val 33) (m.val 34) (m.val 42) A work+1)+32 ∧
      QueryExecution.PrefixBound QueryStreamProgram.nodes (steps+1) a
        (max (919*QueryHeadBudgets.compact A+31)
          (nodeSpace (native).n (m.val 33) (m.val 34) (m.val 42) A)) := by
  sorry

end ActualNode

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect
end
