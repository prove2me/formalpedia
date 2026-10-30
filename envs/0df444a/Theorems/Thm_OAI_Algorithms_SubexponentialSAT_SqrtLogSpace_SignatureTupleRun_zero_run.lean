-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRun_zero_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.zero_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:37:45.557992+00:00
-- url     : https://prove2.me/theorems/d9bbf8a4-a981-4455-8be4-4c72817fe7c9
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.zero_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.zero_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRun.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRun.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun`, with `open Classical`, `open OAI SubexpLiftRing BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage`, `open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram`, `open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource`, `open SignatureTupleComplete`):
--
--   ```lean
--   theorem zero_run (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
--       {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
--       (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
--       (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
--       (hzero : s.input.r=0) (hbound : WordBound F a)
--       (hm : SignatureHeadLoader.MasterFrame s.masters
--         (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
--       (hz : a.stacks 649=unary s.base)
--       (hquery : QueryTupleState.QueryReady q node H high E U P a)
--       (hacc : QueryTupleState.PairAccumulatorMeaning q acc a)
--       (hPF : 4*P+6 ≤ F)
--       (hout : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) ≤ F) :
--       ∃ steps b, Eval SignatureTupleComplete.command steps a b ∧
--         Rel s F q node H high E U P .halt
--           (acc+Dense.readout (1 : Dense (q.p.model.O q.p.t) q.p.t q.J)) b ∧
--         steps+1 ≤ QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J F+
--           1600*(F+1)+2*eventPolynomial s F+2 ∧
--         BitProgram.Trace SignatureTupleComplete.program (steps+1)
--           (a.withPC (some SignatureTupleComplete.program.entry)) (b.withPC none) ∧
--         QueryExecution.PrefixBound SignatureTupleComplete.command (steps+1) a
--           (max (prefixEnvelope s F)
--             (896*F+QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J F+1600*(F+1)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instAdd`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instOneOfZero` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instZero` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.leafRegs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.lowStacks` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum.budget` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal.Cursor` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense.readout` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommSemiring` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.MasterFrame` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.PrefixBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.PairAccumulatorMeaning`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.eventPolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.prefixEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.base`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.headSize`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.key` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.masters` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.Rel` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.RetainedCap` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.command` (definitions bundle `OAIQ081S191` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.program` (definitions bundle `OAIQ081S193` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.run_resources` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRun.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.zero_run)

import Mathlib
import Definitions.Def_OAIQ081S193

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun

open Classical
open OAI SubexpLiftRing BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource
open SignatureTupleComplete

theorem zero_run (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (hzero : s.input.r=0) (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base)
    (hquery : QueryTupleState.QueryReady q node H high E U P a)
    (hacc : QueryTupleState.PairAccumulatorMeaning q acc a)
    (hPF : 4*P+6 ≤ F)
    (hout : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) ≤ F) :
    ∃ steps b, Eval SignatureTupleComplete.command steps a b ∧
      Rel s F q node H high E U P .halt
        (acc+Dense.readout (1 : Dense (q.p.model.O q.p.t) q.p.t q.J)) b ∧
      steps+1 ≤ QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J F+
        1600*(F+1)+2*eventPolynomial s F+2 ∧
      BitProgram.Trace SignatureTupleComplete.program (steps+1)
        (a.withPC (some SignatureTupleComplete.program.entry)) (b.withPC none) ∧
      QueryExecution.PrefixBound SignatureTupleComplete.command (steps+1) a
        (max (prefixEnvelope s F)
          (896*F+QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J F+1600*(F+1))) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun
end
end
