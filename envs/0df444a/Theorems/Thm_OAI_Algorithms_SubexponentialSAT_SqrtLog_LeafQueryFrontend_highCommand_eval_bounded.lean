-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_highCommand_eval_bounded
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highCommand_eval_bounded
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:51:59.877879+00:00
-- url     : https://prove2.me/theorems/6ec8cb1c-6edd-4c4d-a8f2-ee5c5121ba95
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highCommand_eval_bounded: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highCommand_eval_bounded` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendHighBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendHighBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend`, with `open SubexponentialSAT BitProgram StructuredCalls`):
--
--   ```lean
--   theorem highCommand_eval_bounded (a : Data) (rows : List (List ℕ)) (ambient : List Bool)
--       (ha : a.stacks 709=ambient) (hn : 0 < BinaryArithmetic.toNat ambient)
--       (hr : a.stacks 718=LeafStatisticsProgram.scopeBits rows)
--       (he : emptyRange a 417 494) (hh : emptyRange a 580 612)
--       (ht : a.stacks 679=[]) (h338 : a.stacks 338=[])
--       (h719 : a.stacks 719=[]) (h645 : a.stacks 645=[]) (h646 : a.stacks 646=[]) :
--       ∃ n b tau, Eval highCommand n a b ∧
--         BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat ambient) ∧
--         b.stacks 338=highMask rows (BinaryArithmetic.toNat ambient) ∧
--         b.stacks 719=(highMask rows (BinaryArithmetic.toNat ambient)).reverse ∧
--         n ≤ 7*ambient.length+5+EarlyThreshold.runtimeBound ambient+
--           (7*(LeafStatisticsProgram.scopeBits rows).length+5+7*ambient.length+5+7*tau.length+5)+
--           HighIncidenceProgram.Prepare.budget rows ambient tau+1+
--           17*(highMask rows (BinaryArithmetic.toNat ambient)).length+14 ∧
--         (∀ i : Fin 768, (i.val < 417 ∨ 494 ≤ i.val) → (i.val < 580 ∨ 612 ≤ i.val) →
--           i≠338 → i≠719 → i≠645 → i≠646 → b.stacks i=a.stacks i) ∧
--         tau.length ≤ Asymptotic.L (BinaryArithmetic.toNat ambient)+1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.L` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.EarlyThreshold.threshold` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.EarlyThreshold.runtimeBound` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.budget` (definitions bundle `OAIQ081S052` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highMask` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.scopeBits` (definitions bundle `OAIQ081S059` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.emptyRange` (definitions bundle `OAIQ081S093` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highCommand` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval_bounded` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendHighBound.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highCommand_eval_bounded)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S169

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

set_option maxHeartbeats 3200000 in
theorem highCommand_eval_bounded (a : Data) (rows : List (List ℕ)) (ambient : List Bool)
    (ha : a.stacks 709=ambient) (hn : 0 < BinaryArithmetic.toNat ambient)
    (hr : a.stacks 718=LeafStatisticsProgram.scopeBits rows)
    (he : emptyRange a 417 494) (hh : emptyRange a 580 612)
    (ht : a.stacks 679=[]) (h338 : a.stacks 338=[])
    (h719 : a.stacks 719=[]) (h645 : a.stacks 645=[]) (h646 : a.stacks 646=[]) :
    ∃ n b tau, Eval highCommand n a b ∧
      BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat ambient) ∧
      b.stacks 338=highMask rows (BinaryArithmetic.toNat ambient) ∧
      b.stacks 719=(highMask rows (BinaryArithmetic.toNat ambient)).reverse ∧
      n ≤ 7*ambient.length+5+EarlyThreshold.runtimeBound ambient+
        (7*(LeafStatisticsProgram.scopeBits rows).length+5+7*ambient.length+5+7*tau.length+5)+
        HighIncidenceProgram.Prepare.budget rows ambient tau+1+
        17*(highMask rows (BinaryArithmetic.toNat ambient)).length+14 ∧
      (∀ i : Fin 768, (i.val < 417 ∨ 494 ≤ i.val) → (i.val < 580 ∨ 612 ≤ i.val) →
        i≠338 → i≠719 → i≠645 → i≠646 → b.stacks i=a.stacks i) ∧
      tau.length ≤ Asymptotic.L (BinaryArithmetic.toNat ambient)+1 := by
  sorry

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end
