-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadAcceptedCorrect_accepted_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.accepted_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:12:04.932298+00:00
-- url     : https://prove2.me/theorems/31d42ee6-08ad-4231-abc2-20558ef78031
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.accepted_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.accepted_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedCorrect.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedCorrect.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect`, with `open OAI BitProgram StructuredCalls SubexpSetupStorage`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram MomentsProgram`, `open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing`, `open FactorAssignmentProgram FactorAssignmentBoundary QueryTupleState`, `open HighQueryAdapter TruncatedRingProgram`):
--
--   ```lean
--   theorem accepted_eval {node : Fin Q} {H : Finset (Fin n)} {high : H → Bool}
--       {E U : Finset (Fin n)} {a : FactorAssignmentProgram.Data}
--       (hq : QueryReady q node H high E U M a) (ha : WordBound P a)
--       (seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
--       (hseed : Good ∅ q.u q.J seed) (hseedWord : a.stacks 853 = Product.bytes seed)
--       (hlow : ∀ i : Fin 56, a.stacks (i.castAdd 840) = [])
--       (hs0 : a.stacks 883 = []) (hs1 : a.stacks 884 = [])
--       (hh : (a.stacks 859).length = HighIncidenceProgram.Restriction.highCount (a.stacks 670))
--       (hm : (a.stacks 670).length = (a.stacks 869).length)
--       (hn : (a.stacks 670).length = n)
--       (hcache : 4*M+6 ≤ P)
--       (hcapacity : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J ≤ P)
--       (hsize : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
--         (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S)
--       (hradius : q.p.R+1 ≤ Q)
--       (ids : List ℕ) (hids : a.stacks 175 = ProgramEncoding.encodeRecords (FactorAssignmentLoop.records ids))
--       (width Z : ℕ)
--       (hwidth : ∀ f (hf : f < q.rows.length),
--         ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
--           w.literals.length ≤ width)
--       (hZ : 1 ≤ Z) (hP : P ≤ Z) (hbit : q.bitWidth ≤ Z)
--       (hshape : d * baseWidth 3 q.p.t ≤ Z)
--       (hhashScale : ∀ f (hf : f < q.rows.length),
--         FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
--           width q.rows[f].length q.digits.length ≤ Z)
--       (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
--         q.markedClause.length 0 0 ≤ Z) :
--       ∃ (overlaySteps : ℕ) (overlaid : FactorAssignmentProgram.Data) (steps : ℕ) (b : FactorAssignmentProgram.Data)
--         (out : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d),
--         Eval NativeOverlay.prepare overlaySteps a overlaid ∧
--         Eval HeadSumAssembly.accepted steps a b ∧ steps ≤ budget q P S Z ∧
--         Good ∅ q.u q.J out ∧ b.stacks 853 = Product.bytes out ∧
--         rawValue q.u q.J q.p.ops.decode out = rawValue q.u q.J q.p.ops.decode seed +
--           QueryEvaluation.specializeDense q.u q.J
--             (fun v => decide (v ∈ Squarefree.decodeMask n (overlaid.stacks 857)))
--             (Squarefree.canonical q.u q.J ((ids.map (q.value (overlaid.stacks ∘ lowStack))).prod)) ∧
--         WordBound P b ∧ QueryReady q node H high E U M b ∧
--         (∀ i : Fin 56, b.stacks (i.castAdd 840) = []) ∧ b.stacks 854 = [] ∧
--         (∀ i ∈ framePorts, b.stacks i = a.stacks i) ∧
--         (∀ i, i ∉ NativeOverlay.changed → i ∉ entryScratch →
--           i ∉ cachePorts.map lowStack → i ∉ FactorEnvironment.environmentPorts →
--           i ≠ 853 → i ≠ 854 → b.stacks i = a.stacks i) ∧
--         Trace (compiled HeadSumAssembly.accepted 859 853) (steps+1)
--           (a.withPC (some (compiled HeadSumAssembly.accepted 859 853).entry)) (b.withPC none) ∧
--         (∀ j z, j ≤ steps+1 → Trace (compiled HeadSumAssembly.accepted 859 853) j
--           (a.withPC (some (compiled HeadSumAssembly.accepted 859 853).entry)) z →
--           dataBits z ≤ 896*P + budget q P S Z + 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Support` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Triple` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.decodeMask` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instAdd` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop.byteBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.lowStack`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment.environmentPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.inputScale`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.specializedPayloadBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalRecordBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.framePorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeOverlay.changed` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.dataBits` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.ProgramEncoding.encodeRecords` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Jet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ZJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.canonical` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.instCommMonoidSupportOfDecidableEq` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.highCount` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop.records` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.entryScratch` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.cachePorts` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.encodedClauses` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEvaluation.specializeDense` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommSemiring` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.weightedRow` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.WeightedClause` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop.Raw`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.Good` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.rawValue` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ops` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeOverlay.prepare` (definitions bundle `OAIQ081S162` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.digits` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.markedClause` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.value` (definitions bundle `OAIQ081S181` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryReady` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.budget` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly.accepted` (definitions bundle `OAIQ081S191` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumNative_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedCorrect.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.accepted_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect

open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram MomentsProgram
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram FactorAssignmentBoundary QueryTupleState
open HighQueryAdapter TruncatedRingProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q n d P M S : ℕ} {q : Factor.Spec r Q n d}

theorem accepted_eval {node : Fin Q} {H : Finset (Fin n)} {high : H → Bool}
    {E U : Finset (Fin n)} {a : FactorAssignmentProgram.Data}
    (hq : QueryReady q node H high E U M a) (ha : WordBound P a)
    (seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (hseed : Good ∅ q.u q.J seed) (hseedWord : a.stacks 853 = Product.bytes seed)
    (hlow : ∀ i : Fin 56, a.stacks (i.castAdd 840) = [])
    (hs0 : a.stacks 883 = []) (hs1 : a.stacks 884 = [])
    (hh : (a.stacks 859).length = HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length = (a.stacks 869).length)
    (hn : (a.stacks 670).length = n)
    (hcache : 4*M+6 ≤ P)
    (hcapacity : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J ≤ P)
    (hsize : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
      (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S)
    (hradius : q.p.R+1 ≤ Q)
    (ids : List ℕ) (hids : a.stacks 175 = ProgramEncoding.encodeRecords (FactorAssignmentLoop.records ids))
    (width Z : ℕ)
    (hwidth : ∀ f (hf : f < q.rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length ≤ width)
    (hZ : 1 ≤ Z) (hP : P ≤ Z) (hbit : q.bitWidth ≤ Z)
    (hshape : d * baseWidth 3 q.p.t ≤ Z)
    (hhashScale : ∀ f (hf : f < q.rows.length),
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length ≤ Z)
    (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0 ≤ Z) :
    ∃ (overlaySteps : ℕ) (overlaid : FactorAssignmentProgram.Data) (steps : ℕ) (b : FactorAssignmentProgram.Data)
      (out : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d),
      Eval NativeOverlay.prepare overlaySteps a overlaid ∧
      Eval HeadSumAssembly.accepted steps a b ∧ steps ≤ budget q P S Z ∧
      Good ∅ q.u q.J out ∧ b.stacks 853 = Product.bytes out ∧
      rawValue q.u q.J q.p.ops.decode out = rawValue q.u q.J q.p.ops.decode seed +
        QueryEvaluation.specializeDense q.u q.J
          (fun v => decide (v ∈ Squarefree.decodeMask n (overlaid.stacks 857)))
          (Squarefree.canonical q.u q.J ((ids.map (q.value (overlaid.stacks ∘ lowStack))).prod)) ∧
      WordBound P b ∧ QueryReady q node H high E U M b ∧
      (∀ i : Fin 56, b.stacks (i.castAdd 840) = []) ∧ b.stacks 854 = [] ∧
      (∀ i ∈ framePorts, b.stacks i = a.stacks i) ∧
      (∀ i, i ∉ NativeOverlay.changed → i ∉ entryScratch →
        i ∉ cachePorts.map lowStack → i ∉ FactorEnvironment.environmentPorts →
        i ≠ 853 → i ≠ 854 → b.stacks i = a.stacks i) ∧
      Trace (compiled HeadSumAssembly.accepted 859 853) (steps+1)
        (a.withPC (some (compiled HeadSumAssembly.accepted 859 853).entry)) (b.withPC none) ∧
      (∀ j z, j ≤ steps+1 → Trace (compiled HeadSumAssembly.accepted 859 853) j
        (a.withPC (some (compiled HeadSumAssembly.accepted 859 853).entry)) z →
        dataBits z ≤ 896*P + budget q P S Z + 1) := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect
end
