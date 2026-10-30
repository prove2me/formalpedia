-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics_representativeWord_selected
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.representativeWord_selected
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:40:35.672658+00:00
-- url     : https://prove2.me/theorems/3b02e237-d543-4b3a-b053-94d4236c91f8
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.representativeWord_selected: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.representativeWord_selected` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorSemantics.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorSemantics.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics`, with `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open SubexpSetupStorage LeafHeadSetupProgram`, `open SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram`, `open QueryTupleState QueryTupleVisitor SignatureTupleProgram SignatureTupleSource`, `open scoped BigOperators`):
--
--   ```lean
--   theorem representativeWord_selected (s : ProducedSource) {d : ℕ}
--       (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
--       (H : Finset (Fin s.input.n)) (owner : Fin q.ps.length → Fin s.input.n)
--       (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
--       (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head) (g : Fin s.input.r)
--       (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) k → Bool) :
--       QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g reps=
--         HighIncidenceProgram.Restriction.selected true (mask s (s.base+g.val))
--           (List.ofFn (SignatureTupleWords.ambientAssignment H (head s.input.node) g (reps g)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.Head` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbedding.Free` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleWords.ambientAssignment` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.base` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.SourceFacts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.representativeWord` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.mask` (definitions bundle `OAIQ081S185` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.visitor_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorSemantics.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.representativeWord_selected)

import Mathlib
import Definitions.Def_OAIQ081S185

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SubexpSetupStorage LeafHeadSetupProgram
open SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SignatureTupleSource

open scoped BigOperators

theorem representativeWord_selected (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head) (g : Fin s.input.r)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) k → Bool) :
    QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g reps=
      HighIncidenceProgram.Restriction.selected true (mask s (s.base+g.val))
        (List.ofFn (SignatureTupleWords.ambientAssignment H (head s.input.node) g (reps g))) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
end
end
