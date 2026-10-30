-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation_prepare_native_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_native_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:35:41.753709+00:00
-- url     : https://prove2.me/theorems/796b5847-dad6-41d3-8605-feecb817a02f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_native_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_native_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeEvaluation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeEvaluation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation`, with `open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage`, `open LeafHeadSetupProgram QueryTupleState`, `open LeafParametersProgram LeafProgram LeafProgram.PreparedSource`):
--
--   ```lean
--   theorem prepare_native_run
--       (s : Native.Inputs) (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
--       (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
--       (cache : RingProgram.ScalarCache 3 (m.val 33))
--       (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
--       (base out : State 40 768) (ho : Query.ArithmeticOutput base out m hd M cache half e)
--       (hfield : s.Q < 3^(m.val 34)) (hQ : m.val 21=s.Q)
--       (hR : (base.stacks 740).length=s.R) (q : LeafQueryFrontend.Query) (hv : q.Valid)
--       (hJ : 0 < m.val 42) (source : List (List (SAT.Literal (Fin s.n))))
--       (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)
--       (H : Finset (Fin s.n)) (high : H → Bool) (B : ℕ) (a : Data)
--       (hbank : NativeLayoutLoad.SourceBank s a)
--       (tail : List (List Bool))
--       (hcursor : a.stacks 301=Encoding.encodeList id
--         (RingProgram.flat (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (s.node.val+1))::tail))
--       (hmask : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
--       (hframe : ∀ i ∈ QueryReadyConstruction.arithmeticPorts,a.stacks (i.castAdd 128)=out.stacks i)
--       (hdegree : out.stacks 204=List.replicate (m.val 34) true)
--       (h700 : a.stacks 700=Encoding.encodeList id q.clauses)
--       (h701 : a.stacks 701=HashScopeProgram.RawTable.inputBits q.width.length q.rows)
--       (h704 : a.stacks 704=List.replicate q.rows.length true)
--       (h705 : a.stacks 705=Encoding.encodeNat (markIndex q))
--       (h706 : a.stacks 706=[q.mark.isSome])
--       (h707 : a.stacks 707=q.modulus) (h708 : a.stacks 708=q.width)
--       (h702 : a.stacks 702=List.ofFn (fun v : Fin s.n => decide (v ∈ H)))
--       (h703 : a.stacks 703=List.ofFn (fun v : Fin s.n => if h:v ∈ H then high ⟨v,h⟩ else false))
--       (hb : WordBound B a) (hcap : SignatureHeadLoader.bootstrapOutputBound s ≤ B) :
--       ∃ (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)),
--       ∃ hw : CacheCorrect s.height (unary s.R) s.width words, ∃ ticks b,
--         let snap := sourceSnapshot a
--           (RingProgram.flat (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (s.node.val+1))) tail
--         let spec := nativeSpecOfInputs s m ht hd words hw M cache half e ho.produced
--           hfield q hv (m.val 42) hJ source hsource
--         Eval prepareNode ticks a b ∧ ticks ≤ 20000*(B+1)^4+300*(B+1) ∧
--         WordBound B b ∧ QueryReadyConstruction.CommonReady spec s.node H high B b ∧
--         QueryPairCommit.NodeAccumulatorMeaning spec 0 b ∧ PairAccumulatorMeaning spec 0 b ∧
--         b.stacks 832=List.replicate (s.n-H.card) true ∧ b.stacks 833=List.replicate spec.J true ∧
--         b.stacks 834=[] ∧ b.stacks 835=[] ∧
--         b.stacks 301=Encoding.encodeList id tail ∧ b.stacks 307=a.stacks 307 ∧
--         b.stacks 863=a.stacks 863 ∧ (∀ i ∈ framePorts,b.stacks i=a.stacks i) ∧
--         Native.Ready s snap ∧ WordBound B snap ∧
--         SignatureHeadLoader.MasterFrame (Native.start s snap ra rd rc words)
--           (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) ∧
--         b.stacks 649=unary (s.node.val*s.r) ∧
--         Trace (compiled prepareNode 301 832) (ticks+1)
--           (a.withPC (some (compiled prepareNode 301 832).entry)) (b.withPC none) ∧
--         ∀ k z,k ≤ ticks+1 → Trace (compiled prepareNode 301 832) k
--           (a.withPC (some (compiled prepareNode 301 832).entry)) z →
--           ∀ i,(z.stacks i).length ≤ 896*B+20000*(B+1)^4+300*(B+1)+1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instZero` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.framePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction.arithmeticPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.leafRegs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.lowStacks` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.inputBits` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Data` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram.descendingHighMask` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.encodedClauses` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.CacheCorrect` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.bootstrapOutputBound` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgram.nodeCode` (definitions bundle `OAIQ081S122` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Ready` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.MasterFrame` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad.SourceBank` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.start` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepareNode` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.markIndex` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.ArithmeticOutput` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit.NodeAccumulatorMeaning` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.PairAccumulatorMeaning` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.nativeSpecOfInputs` (definitions bundle `OAIQ081S181` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.sourceSnapshot` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction.CommonReady` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.node_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeEvaluation.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_native_run)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S181
import Definitions.Def_OAIQ081S185

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

theorem prepare_native_run
    (s : Native.Inputs) (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (base out : State 40 768) (ho : Query.ArithmeticOutput base out m hd M cache half e)
    (hfield : s.Q < 3^(m.val 34)) (hQ : m.val 21=s.Q)
    (hR : (base.stacks 740).length=s.R) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (hJ : 0 < m.val 42) (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (H : Finset (Fin s.n)) (high : H → Bool) (B : ℕ) (a : Data)
    (hbank : NativeLayoutLoad.SourceBank s a)
    (tail : List (List Bool))
    (hcursor : a.stacks 301=Encoding.encodeList id
      (RingProgram.flat (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (s.node.val+1))::tail))
    (hmask : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (hframe : ∀ i ∈ QueryReadyConstruction.arithmeticPorts,a.stacks (i.castAdd 128)=out.stacks i)
    (hdegree : out.stacks 204=List.replicate (m.val 34) true)
    (h700 : a.stacks 700=Encoding.encodeList id q.clauses)
    (h701 : a.stacks 701=HashScopeProgram.RawTable.inputBits q.width.length q.rows)
    (h704 : a.stacks 704=List.replicate q.rows.length true)
    (h705 : a.stacks 705=Encoding.encodeNat (markIndex q))
    (h706 : a.stacks 706=[q.mark.isSome])
    (h707 : a.stacks 707=q.modulus) (h708 : a.stacks 708=q.width)
    (h702 : a.stacks 702=List.ofFn (fun v : Fin s.n => decide (v ∈ H)))
    (h703 : a.stacks 703=List.ofFn (fun v : Fin s.n => if h:v ∈ H then high ⟨v,h⟩ else false))
    (hb : WordBound B a) (hcap : SignatureHeadLoader.bootstrapOutputBound s ≤ B) :
    ∃ (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)),
    ∃ hw : CacheCorrect s.height (unary s.R) s.width words, ∃ ticks b,
      let snap := sourceSnapshot a
        (RingProgram.flat (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (s.node.val+1))) tail
      let spec := nativeSpecOfInputs s m ht hd words hw M cache half e ho.produced
        hfield q hv (m.val 42) hJ source hsource
      Eval prepareNode ticks a b ∧ ticks ≤ 20000*(B+1)^4+300*(B+1) ∧
      WordBound B b ∧ QueryReadyConstruction.CommonReady spec s.node H high B b ∧
      QueryPairCommit.NodeAccumulatorMeaning spec 0 b ∧ PairAccumulatorMeaning spec 0 b ∧
      b.stacks 832=List.replicate (s.n-H.card) true ∧ b.stacks 833=List.replicate spec.J true ∧
      b.stacks 834=[] ∧ b.stacks 835=[] ∧
      b.stacks 301=Encoding.encodeList id tail ∧ b.stacks 307=a.stacks 307 ∧
      b.stacks 863=a.stacks 863 ∧ (∀ i ∈ framePorts,b.stacks i=a.stacks i) ∧
      Native.Ready s snap ∧ WordBound B snap ∧
      SignatureHeadLoader.MasterFrame (Native.start s snap ra rd rc words)
        (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) ∧
      b.stacks 649=unary (s.node.val*s.r) ∧
      Trace (compiled prepareNode 301 832) (ticks+1)
        (a.withPC (some (compiled prepareNode 301 832).entry)) (b.withPC none) ∧
      ∀ k z,k ≤ ticks+1 → Trace (compiled prepareNode 301 832) k
        (a.withPC (some (compiled prepareNode 301 832).entry)) z →
        ∀ i,(z.stacks i).length ≤ 896*B+20000*(B+1)^4+300*(B+1)+1 := by
  sorry

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end
