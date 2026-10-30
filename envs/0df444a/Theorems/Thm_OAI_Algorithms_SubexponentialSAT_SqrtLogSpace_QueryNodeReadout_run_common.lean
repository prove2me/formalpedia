-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeReadout_run_common
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout.run_common
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:37:05.30976+00:00
-- url     : https://prove2.me/theorems/604e949a-3d66-407c-8f23-1cdb947da5db
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout.run_common: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout.run_common` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeReadout.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeReadout.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout`, with `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing`, `open LeafProgram MomentsProgram LayoutProgram TruncatedRingProgram QueryTupleState`, `open QueryPairCommit QueryReadyConstruction`):
--
--   ```lean
--   theorem run_common {r Q n d : ℕ} (q : Factor.Spec r Q n d) (node : Fin Q)
--       (H : Finset (Fin n)) (high : H → Bool)
--       (P B index : ℕ) (a : Data)
--       (hready : CommonReady q node H high P a)
--       (value : Truncated (q.p.model.O q.p.t) q.J)
--       (hvalue : NodeAccumulatorMeaning q value a)
--       (remaining : List (List Bool))
--       (hcursor : a.stacks 301=Encoding.encodeList id remaining)
--       (hindex : a.stacks 307=List.replicate index true)
--       (hb : ∀ i, (a.stacks i).length ≤ B)
--       (hout : (a.stacks 863).length + q.J * (d * baseWidth 3 q.p.t) ≤ B)
--       (hnext : index + 1 ≤ B) :
--       ∃ steps b, ∃ codes : List (RingProgram.Code (Word (baseWidth 3 q.p.t)) d),
--         Eval QueryNodeFinish.command steps a b ∧ codes.length=q.J ∧
--         codes.map q.p.ops.decode=List.ofFn value.coeff ∧
--         b.stacks 863=a.stacks 863++(codes.map RingProgram.flat).flatten ∧
--         b.stacks 78=[] ∧ b.stacks 850=[] ∧ b.stacks 862=[] ∧
--         (∀ i∈NodeReadoutSpace.scratchPorts,b.stacks i=[]) ∧
--         b.stacks 307=List.replicate (index+1) true ∧
--         b.regs 37= !remaining.isEmpty ∧ b.regs 38=true ∧
--         (∀ i,i∉QueryNodeFinish.touchedPorts → b.stacks i=a.stacks i) ∧
--         (∀ i, (b.stacks i).length ≤ B) ∧
--         steps + 1 ≤ QueryNodeFinish.budget n (baseWidth 3 q.p.t) d q.p.t q.J B ∧
--         Trace QueryNodeFinish.program (steps + 1)
--           (a.withPC (some QueryNodeFinish.program.entry)) (b.withPC none) ∧
--         ∀ (prefixSteps : ℕ) intermediate, prefixSteps ≤ steps + 1 →
--           Trace QueryNodeFinish.program prefixSteps
--             (a.withPC (some QueryNodeFinish.program.entry)) intermediate →
--           ∀ i, (intermediate.stacks i).length ≤
--             896 * B + QueryNodeFinish.budget n (baseWidth 3 q.p.t) d q.p.t q.J B
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace.scratchPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.touchedPorts` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.budget` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ops` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit.NodeAccumulatorMeaning` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction.CommonReady` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeReadout.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout.run_common)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram TruncatedRingProgram QueryTupleState
open QueryPairCommit QueryReadyConstruction

theorem run_common {r Q n d : ℕ} (q : Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool)
    (P B index : ℕ) (a : Data)
    (hready : CommonReady q node H high P a)
    (value : Truncated (q.p.model.O q.p.t) q.J)
    (hvalue : NodeAccumulatorMeaning q value a)
    (remaining : List (List Bool))
    (hcursor : a.stacks 301=Encoding.encodeList id remaining)
    (hindex : a.stacks 307=List.replicate index true)
    (hb : ∀ i, (a.stacks i).length ≤ B)
    (hout : (a.stacks 863).length + q.J * (d * baseWidth 3 q.p.t) ≤ B)
    (hnext : index + 1 ≤ B) :
    ∃ steps b, ∃ codes : List (RingProgram.Code (Word (baseWidth 3 q.p.t)) d),
      Eval QueryNodeFinish.command steps a b ∧ codes.length=q.J ∧
      codes.map q.p.ops.decode=List.ofFn value.coeff ∧
      b.stacks 863=a.stacks 863++(codes.map RingProgram.flat).flatten ∧
      b.stacks 78=[] ∧ b.stacks 850=[] ∧ b.stacks 862=[] ∧
      (∀ i∈NodeReadoutSpace.scratchPorts,b.stacks i=[]) ∧
      b.stacks 307=List.replicate (index+1) true ∧
      b.regs 37= !remaining.isEmpty ∧ b.regs 38=true ∧
      (∀ i,i∉QueryNodeFinish.touchedPorts → b.stacks i=a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) ∧
      steps + 1 ≤ QueryNodeFinish.budget n (baseWidth 3 q.p.t) d q.p.t q.J B ∧
      Trace QueryNodeFinish.program (steps + 1)
        (a.withPC (some QueryNodeFinish.program.entry)) (b.withPC none) ∧
      ∀ (prefixSteps : ℕ) intermediate, prefixSteps ≤ steps + 1 →
        Trace QueryNodeFinish.program prefixSteps
          (a.withPC (some QueryNodeFinish.program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          896 * B + QueryNodeFinish.budget n (baseWidth 3 q.p.t) d q.p.t q.J B := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout
end
