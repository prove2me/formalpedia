-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_numericStage_eval_bounded
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericStage_eval_bounded
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:52:00.507341+00:00
-- url     : https://prove2.me/theorems/f72e5d62-8393-47ef-964c-bafaaa52ae6c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericStage_eval_bounded: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericStage_eval_bounded` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendNumericBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendNumericBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend`, with `open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram`):
--
--   ```lean
--   theorem numericStage_eval_bounded (a : Data) (ambient clauses : List Bool)
--       (k free occ arity factors mass : ℕ)
--       (ha : a.stacks 709=ambient) (hm : a.stacks 707=clauses)
--       (hz : emptyRange a 340 417) (ht : a.stacks 679=[]) (ht' : a.stacks 647=[])
--       (hfree : a.stacks 626=List.replicate free true)
--       (hocc : a.stacks 627=List.replicate occ true)
--       (harity : a.stacks 642=List.replicate arity true)
--       (hfactors : a.stacks 613=List.replicate factors true)
--       (hmass : a.stacks 628=List.replicate mass true) :
--       ∃ n b l w, Eval (numericStage k) n a b ∧
--         projectState r9 bank b=Execute.state (b.regs ∘ r9) w ∧
--         Circuit.Shape (Layout.initialModel (numericInput ambient clauses k free occ arity factors mass) l) w ∧
--         n ≤ numericCost ambient clauses k free occ arity factors mass ∧
--         (∀ i : Fin 768, (i.val < 340 ∨ 417 ≤ i.val) →
--           i≠626 → i≠627 → i≠642 → i≠613 → i≠628 → i≠647 → b.stacks i=a.stacks i) ∧
--         l=(fun _ => numericCost ambient clauses k free occ arity factors mass)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericCost` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.bank` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.r9` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.state` (definitions bundle `OAIQ081S083` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.emptyRange` (definitions bundle `OAIQ081S093` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Shape` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericStage` (definitions bundle `OAIQ081S130` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout.initialModel` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericInput` (definitions bundle `OAIQ081S168` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval_bounded` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendNumericBound.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericStage_eval_bounded)

import Mathlib
import Definitions.Def_OAIQ081S168

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem numericStage_eval_bounded (a : Data) (ambient clauses : List Bool)
    (k free occ arity factors mass : ℕ)
    (ha : a.stacks 709=ambient) (hm : a.stacks 707=clauses)
    (hz : emptyRange a 340 417) (ht : a.stacks 679=[]) (ht' : a.stacks 647=[])
    (hfree : a.stacks 626=List.replicate free true)
    (hocc : a.stacks 627=List.replicate occ true)
    (harity : a.stacks 642=List.replicate arity true)
    (hfactors : a.stacks 613=List.replicate factors true)
    (hmass : a.stacks 628=List.replicate mass true) :
    ∃ n b l w, Eval (numericStage k) n a b ∧
      projectState r9 bank b=Execute.state (b.regs ∘ r9) w ∧
      Circuit.Shape (Layout.initialModel (numericInput ambient clauses k free occ arity factors mass) l) w ∧
      n ≤ numericCost ambient clauses k free occ arity factors mass ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 417 ≤ i.val) →
        i≠626 → i≠627 → i≠642 → i≠613 → i≠628 → i≠647 → b.stacks i=a.stacks i) ∧
      l=(fun _ => numericCost ambient clauses k free occ arity factors mass) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end
