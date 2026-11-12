-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:01:42.004478+00:00
-- url     : https://prove2.me/theorems/74f28140-3bae-42d3-bae3-308aaae48214
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchPhysical.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchPhysical.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram`, with `open WordOperations WordList BinaryBranchContext`, `open BinaryOpeningPayment (field field_encode)`):
--
--   ```lean
--   lemma run_pack_s238r (hp : plan d data=encode [BinaryFinSet.table sel,BinaryFinSet.table dest])
--       (bits : Categorical.BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length
--         (Categorical.Explicit.exponent s.leaves.length) (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) :
--       run d (pairBits (data,BinaryCategorical.Tape.raw (s.leaves.length*n) s.leaves.length
--         (Categorical.Explicit.exponent s.leaves.length) (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length) bits))=
--         BinaryFinSet.encode (BinaryCompletionFair.result F S s.deleted Completion.CopyGround.part
--           (Completion.CopyGround.part_surjective (balls δ F s) hH) (Completion.CopyGround.origin (balls δ F s) hH)
--           loc (SortedIndex.enum red) sel dest k bas dst wt rb rd bits)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Categorical.BinaryOracleIndex`, `OAI.MetricKMedianRecovery.RationalSampling.State`, `OAI.MetricKMedianRecovery.RationalSampling.assignmentWeight`, `OAI.MetricKMedianRecovery.RationalSampling.reference`, `OAI.MetricKMedianRecovery.SortedIndex.enum`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.balls`, `OAI.MetricKMedianRecovery.Categorical.Explicit.exponent`, `OAI.MetricKMedianRecovery.Categorical.Explicit.samples`, `OAI.MetricKMedianRecovery.Completion.CopyGround.location`, `OAI.MetricKMedianRecovery.Completion.CopyGround.origin`, `OAI.MetricKMedianRecovery.Completion.CopyGround.part` and `OAI.MetricKMedianRecovery.Completion.CopyGround.part_surjective` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238L006` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape.raw` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.table` (definitions bundle `Q238L018` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.pack` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.plan` (definitions bundle `Q238L033` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run` (definitions bundle `Q238L037` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchPhysical.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open WordOperations WordList BinaryBranchContext
open BinaryOpeningPayment (field field_encode)
variable {n m : ℕ}
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (k c : ℕ) (extra : List Bool)
local notation "data" => BinaryBranchContext.pack δ D F S Δ s colors label k c extra
local notation "red" => Finset.filter (fun i=>colors i=1) (S\RationalSampling.State.deleted s)
local notation "green" => Finset.filter (fun i=>colors i=0) (S\RationalSampling.State.deleted s)
variable (hH : ∀ i,(balls δ F s i).Nonempty)
local notation "loc" => Completion.CopyGround.location (balls δ F s) hH
local notation "wt" => (fun i=>RationalSampling.assignmentWeight δ D S Δ s (SortedIndex.enum red i))
local notation "rb" => (fun i=>RationalSampling.reference δ green Δ (RationalSampling.State.mk ∅ (RationalSampling.State.leaves s)) (SortedIndex.enum red i))
local notation "bas" => (fun i=>RationalSampling.reference δ S Δ s (SortedIndex.enum D i))
local notation "dst" => (fun i e=>δ (SortedIndex.enum D i) (loc e))
local notation "rd" => (fun i e=>δ (SortedIndex.enum red i) (loc e))
variable (d : ℕ) (sel dest : Fin m→Fin n)
lemma run_pack_s238r (hp : plan d data=encode [BinaryFinSet.table sel,BinaryFinSet.table dest])
    (bits : Categorical.BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length
      (Categorical.Explicit.exponent s.leaves.length) (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) :
    run d (pairBits (data,BinaryCategorical.Tape.raw (s.leaves.length*n) s.leaves.length
      (Categorical.Explicit.exponent s.leaves.length) (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length) bits))=
      BinaryFinSet.encode (BinaryCompletionFair.result F S s.deleted Completion.CopyGround.part
        (Completion.CopyGround.part_surjective (balls δ F s) hH) (Completion.CopyGround.origin (balls δ F s) hH)
        loc (SortedIndex.enum red) sel dest k bas dst wt rb rd bits) := by
  sorry
end Correct
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end
