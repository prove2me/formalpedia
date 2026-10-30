-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_convertStatistics_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.convertStatistics_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:33:42.151887+00:00
-- url     : https://prove2.me/theorems/be18565d-b60b-4425-995f-1a9fa8b22acd
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.convertStatistics_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.convertStatistics_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendConvert.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendConvert.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend`, with `open SubexponentialSAT BitProgram StructuredCalls`):
--
--   ```lean
--   theorem convertStatistics_eval (a : Data) (free occ arity factors mass : ℕ)
--       (ht : a.stacks 647=[])
--       (h626 : a.stacks 626=List.replicate free true)
--       (h341 : a.stacks 341=[])
--       (h627 : a.stacks 627=List.replicate occ true)
--       (h343 : a.stacks 343=[])
--       (h642 : a.stacks 642=List.replicate arity true)
--       (h344 : a.stacks 344=[])
--       (h613 : a.stacks 613=List.replicate factors true)
--       (h345 : a.stacks 345=[])
--       (h628 : a.stacks 628=List.replicate mass true)
--       (h347 : a.stacks 347=[])
--       : ∃ n b, Eval convertStatistics n a b ∧
--         n ≤ conversionCost free + conversionCost occ + conversionCost arity + conversionCost factors + conversionCost mass ∧
--         BinaryArithmetic.toNat (b.stacks 341)=free ∧
--         (b.stacks 341).length ≤ free ∧
--         BinaryArithmetic.toNat (b.stacks 343)=occ ∧
--         (b.stacks 343).length ≤ occ ∧
--         BinaryArithmetic.toNat (b.stacks 344)=arity ∧
--         (b.stacks 344).length ≤ arity ∧
--         BinaryArithmetic.toNat (b.stacks 345)=factors ∧
--         (b.stacks 345).length ≤ factors ∧
--         BinaryArithmetic.toNat (b.stacks 347)=mass ∧
--         (b.stacks 347).length ≤ mass ∧
--         b.stacks 647=[] ∧
--         (∀ i : Fin 768, i≠626 → i≠341 → i≠627 → i≠343 → i≠642 → i≠344 → i≠613 → i≠345 → i≠628 → i≠347 → i≠647 → b.stacks i=a.stacks i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.conversionCost` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Data` (definitions bundle `OAIQ081S093` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.convertStatistics` (definitions bundle `OAIQ081S130` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericStage_eval_bounded` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendConvert.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.convertStatistics_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S130

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem convertStatistics_eval (a : Data) (free occ arity factors mass : ℕ)
    (ht : a.stacks 647=[])
    (h626 : a.stacks 626=List.replicate free true)
    (h341 : a.stacks 341=[])
    (h627 : a.stacks 627=List.replicate occ true)
    (h343 : a.stacks 343=[])
    (h642 : a.stacks 642=List.replicate arity true)
    (h344 : a.stacks 344=[])
    (h613 : a.stacks 613=List.replicate factors true)
    (h345 : a.stacks 345=[])
    (h628 : a.stacks 628=List.replicate mass true)
    (h347 : a.stacks 347=[])
    : ∃ n b, Eval convertStatistics n a b ∧
      n ≤ conversionCost free + conversionCost occ + conversionCost arity + conversionCost factors + conversionCost mass ∧
      BinaryArithmetic.toNat (b.stacks 341)=free ∧
      (b.stacks 341).length ≤ free ∧
      BinaryArithmetic.toNat (b.stacks 343)=occ ∧
      (b.stacks 343).length ≤ occ ∧
      BinaryArithmetic.toNat (b.stacks 344)=arity ∧
      (b.stacks 344).length ≤ arity ∧
      BinaryArithmetic.toNat (b.stacks 345)=factors ∧
      (b.stacks 345).length ≤ factors ∧
      BinaryArithmetic.toNat (b.stacks 347)=mass ∧
      (b.stacks 347).length ≤ mass ∧
      b.stacks 647=[] ∧
      (∀ i : Fin 768, i≠626 → i≠341 → i≠627 → i≠343 → i≠642 → i≠344 → i≠613 → i≠345 → i≠628 → i≠347 → i≠647 → b.stacks i=a.stacks i) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end
