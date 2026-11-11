-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryZeroBranch_completion_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:04:19.296314+00:00
-- url     : https://prove2.me/theorems/2144bb25-2035-417c-893b-251f29b1f1da
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/ObservableCapacity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/ObservableCapacity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch`, with `open WordOperations WordList BinaryBranchContext BinaryBranchProgram BinaryArithmetic`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma completion_pack_s238 (hH : ∀ i,(balls δ F s i).Nonempty) :
--       completion data=BinaryCompletionRealize.pack F S s.deleted Completion.CopyGround.part
--         (Completion.CopyGround.origin (balls δ F s) hH) (Completion.CopyGround.location (balls δ F s) hH)
--         (SortedIndex.enum ((S\s.deleted).filter (fun i=>colors i=1))) (Fin.elim0 : Fin 0→Fin n) Fin.elim0 q
--         (fun i=>RationalSampling.reference δ S Δ s (SortedIndex.enum D i))
--         (fun i e=>δ (SortedIndex.enum D i) (Completion.CopyGround.location (balls δ F s) hH e))
--         (fun i=>RationalSampling.assignmentWeight δ D S Δ s (SortedIndex.enum ((S\s.deleted).filter (fun i=>colors i=1)) i))
--         (fun i=>RationalSampling.reference δ ((S\s.deleted).filter (fun i=>colors i=0)) Δ
--           (RationalSampling.State.mk ∅ s.leaves) (SortedIndex.enum ((S\s.deleted).filter (fun i=>colors i=1)) i))
--         (fun i e=>δ (SortedIndex.enum ((S\s.deleted).filter (fun i=>colors i=1)) i)
--           (Completion.CopyGround.location (balls δ F s) hH e)) []
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State`, `OAI.MetricKMedianRecovery.RationalSampling.assignmentWeight`, `OAI.MetricKMedianRecovery.RationalSampling.reference`, `OAI.MetricKMedianRecovery.SortedIndex.enum`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.balls`, `OAI.MetricKMedianRecovery.Completion.CopyGround.location` and `OAI.MetricKMedianRecovery.Completion.CopyGround.part` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Completion.CopyGround.origin` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.pack` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.pack` (definitions bundle `Q238K027` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion` (definitions bundle `Q238K037` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.run_pack_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/ObservableCapacity.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack)

import Mathlib
import Definitions.Def_Q238K027
import Definitions.Def_Q238K037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryZeroBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram BinaryArithmetic
attribute [local instance] Classical.propDecidable
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (q : ℕ) (extra : List Bool)
local notation "data" => pack δ D F S Δ s colors q extra
lemma completion_pack_s238 (hH : ∀ i,(balls δ F s i).Nonempty) :
    completion data=BinaryCompletionRealize.pack F S s.deleted Completion.CopyGround.part
      (Completion.CopyGround.origin (balls δ F s) hH) (Completion.CopyGround.location (balls δ F s) hH)
      (SortedIndex.enum ((S\s.deleted).filter (fun i=>colors i=1))) (Fin.elim0 : Fin 0→Fin n) Fin.elim0 q
      (fun i=>RationalSampling.reference δ S Δ s (SortedIndex.enum D i))
      (fun i e=>δ (SortedIndex.enum D i) (Completion.CopyGround.location (balls δ F s) hH e))
      (fun i=>RationalSampling.assignmentWeight δ D S Δ s (SortedIndex.enum ((S\s.deleted).filter (fun i=>colors i=1)) i))
      (fun i=>RationalSampling.reference δ ((S\s.deleted).filter (fun i=>colors i=0)) Δ
        (RationalSampling.State.mk ∅ s.leaves) (SortedIndex.enum ((S\s.deleted).filter (fun i=>colors i=1)) i))
      (fun i e=>δ (SortedIndex.enum ((S\s.deleted).filter (fun i=>colors i=1)) i)
        (Completion.CopyGround.location (balls δ F s) hH e)) [] := by
  sorry
end Correct
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

end OAI
end
