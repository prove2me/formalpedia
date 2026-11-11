-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_run_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:59:42.487946+00:00
-- url     : https://prove2.me/theorems/eae10c79-54b2-4345-8a79-5666d0253723
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchPhysical.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchPhysical.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram`, with `open WordOperations WordList BinaryBranchContext`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma run_pack_s238 (hp : plan d data=encode [BinaryFinSet.table sel,BinaryFinSet.table dest])
--       (bits : Categorical.BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length
--         (Categorical.Explicit.exponent s.leaves.length) (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) :
--       run d (pairBits (data,BinaryCategorical.Tape.raw (s.leaves.length*n) s.leaves.length
--         (Categorical.Explicit.exponent s.leaves.length) (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length) bits))=
--         BinaryFinSet.encode (BinaryCompletionFair.result F S s.deleted Completion.CopyGround.part
--           (Completion.CopyGround.part_surjective (balls δ F s) hH) (Completion.CopyGround.origin (balls δ F s) hH)
--           loc (SortedIndex.enum red) sel dest k bas dst wt rb rd bits)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.Categorical.BinaryOracleIndex`, `OAI.MetricKMedianRecovery.RationalSampling.State`, `OAI.MetricKMedianRecovery.RationalSampling.assignmentWeight`, `OAI.MetricKMedianRecovery.RationalSampling.reference`, `OAI.MetricKMedianRecovery.SortedIndex.enum`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.balls`, `OAI.MetricKMedianRecovery.Categorical.Explicit.exponent`, `OAI.MetricKMedianRecovery.Categorical.Explicit.samples`, `OAI.MetricKMedianRecovery.Completion.CopyGround.location` and `OAI.MetricKMedianRecovery.Completion.CopyGround.part` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Completion.CopyGround.origin` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` and `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.table` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result` and `OAI.MetricKMedianRecovery.Completion.CopyGround.part_surjective` (definitions bundle `Q238K011` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape.raw` (definitions bundle `Q238K012` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.pack` (definitions bundle `Q238K020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.plan` (definitions bundle `Q238K029` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run` (definitions bundle `Q238K037` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchPhysical.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open WordOperations WordList BinaryBranchContext
open BinaryOpeningPayment (field )
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
lemma run_pack_s238 (hp : plan d data=encode [BinaryFinSet.table sel,BinaryFinSet.table dest])
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
