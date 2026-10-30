-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadAcceptedCorrect_overlay_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.overlay_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:35:18.406924+00:00
-- url     : https://prove2.me/theorems/2b7e22c2-45e4-4152-a1f1-c9fc3993b90c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.overlay_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.overlay_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedCorrect.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedCorrect.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect`, with `open OAI BitProgram StructuredCalls SubexpSetupStorage`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram MomentsProgram`, `open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing`, `open FactorAssignmentProgram FactorAssignmentBoundary QueryTupleState`, `open HighQueryAdapter TruncatedRingProgram`):
--
--   ```lean
--   theorem overlay_eval {a : FactorAssignmentProgram.Data} {P n : ℕ}
--       (ha : WordBound P a)
--       (hh : (a.stacks 859).length = HighIncidenceProgram.Restriction.highCount (a.stacks 670))
--       (hm : (a.stacks 670).length = (a.stacks 869).length)
--       (hn : (a.stacks 670).length = n) :
--       ∃ steps b, Eval NativeOverlay.prepare steps a b ∧ steps ≤ 70*P+70 ∧
--         WordBound P b ∧ (b.stacks 145).length = n ∧
--         ∀ i, i ∉ NativeOverlay.changed → b.stacks i = a.stacks i
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeOverlay.changed` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.highCount` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.Data` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeOverlay.prepare` (definitions bundle `OAIQ081S162` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.accepted_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedCorrect.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.overlay_eval)

import Mathlib
import Definitions.Def_OAIQ081S162

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

theorem overlay_eval {a : FactorAssignmentProgram.Data} {P n : ℕ}
    (ha : WordBound P a)
    (hh : (a.stacks 859).length = HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length = (a.stacks 869).length)
    (hn : (a.stacks 670).length = n) :
    ∃ steps b, Eval NativeOverlay.prepare steps a b ∧ steps ≤ 70*P+70 ∧
      WordBound P b ∧ (b.stacks 145).length = n ∧
      ∀ i, i ∉ NativeOverlay.changed → b.stacks i = a.stacks i := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect
end
