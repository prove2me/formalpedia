-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_objective_eq_source_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.objective_eq_source_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:25:30.727214+00:00
-- url     : https://prove2.me/theorems/508df826-a63f-4746-aef7-9e41b7fc90a0
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.objective_eq_source_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.objective_eq_source` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchObjective.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchObjective.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram`, with `open Completion Categorical FiniteSampling BinaryBranchContext`):
--
--   ```lean
--   lemma objective_eq_source_s238 (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
--       (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
--       (colors : Fin n→Fin 3) (hH : ∀ i,(balls δ F s i).Nonempty) (sel dest : Fin m→Fin n) (k : ℕ)
--       (X : Finset (Fin (s.leaves.length*n))) :
--       objective δ D F S Δ s colors hH sel dest k X=
--       surrogate (∑ j,Sampling.branchScore D S (Δ:ℝ) s.real (sel j) (dest j)) k
--         (fun p : D=>virtualNearest (S\s.deleted) (Sampling.leafCenter s.real) (Sampling.leafRadius s.real) (Δ:ℝ) p)
--         (fun p e=>dist (p:Fin n) (CopyGround.location (balls δ F s) hH e))
--         (fun i : Fin ((S\s.deleted).filter (fun i=>colors i=1)).card=>assignmentWeight D (Sampling.completionAssignment S (Δ:ℝ) s.real) (SortedIndex.enum _ i))
--         (fun i=>virtualNearest ((S\s.deleted).filter (fun i=>colors i=0)) (Sampling.leafCenter s.real) (Sampling.leafRadius s.real) (Δ:ℝ) (SortedIndex.enum _ i))
--         (fun i e=>dist (SortedIndex.enum _ i) (CopyGround.location (balls δ F s) hH e)) X
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Completion.surrogate`, `OAI.MetricKMedianRecovery.RationalSampling.State`, `OAI.MetricKMedianRecovery.SortedIndex.enum`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.balls`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.objective`, `OAI.MetricKMedianRecovery.Completion.CopyGround.location`, `OAI.MetricKMedianRecovery.RationalSampling.State.real` and `OAI.MetricKMedianRecovery.Sampling.State` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Completion.assignmentWeight` and `OAI.MetricKMedianRecovery.Completion.virtualNearest` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.Sampling.completionAssignment` (definitions bundle `Q238K015` of this split); `OAI.MetricKMedianRecovery.Sampling.leafCenter` and `OAI.MetricKMedianRecovery.Sampling.leafRadius` (definitions bundle `Q238K016` of this split); `OAI.MetricKMedianRecovery.Sampling.branchScore` (definitions bundle `Q238K022` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.planned_successful_completion_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.successful_completion_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryZeroBranch_successful_probability_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchObjective.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.objective_eq_source)

import Mathlib
import Definitions.Def_Q238K022

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext
variable {n m : ℕ} [PseudoMetricSpace (Fin n)]
lemma objective_eq_source_s238 (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (hH : ∀ i,(balls δ F s i).Nonempty) (sel dest : Fin m→Fin n) (k : ℕ)
    (X : Finset (Fin (s.leaves.length*n))) :
    objective δ D F S Δ s colors hH sel dest k X=
    surrogate (∑ j,Sampling.branchScore D S (Δ:ℝ) s.real (sel j) (dest j)) k
      (fun p : D=>virtualNearest (S\s.deleted) (Sampling.leafCenter s.real) (Sampling.leafRadius s.real) (Δ:ℝ) p)
      (fun p e=>dist (p:Fin n) (CopyGround.location (balls δ F s) hH e))
      (fun i : Fin ((S\s.deleted).filter (fun i=>colors i=1)).card=>assignmentWeight D (Sampling.completionAssignment S (Δ:ℝ) s.real) (SortedIndex.enum _ i))
      (fun i=>virtualNearest ((S\s.deleted).filter (fun i=>colors i=0)) (Sampling.leafCenter s.real) (Sampling.leafRadius s.real) (Δ:ℝ) (SortedIndex.enum _ i))
      (fun i e=>dist (SortedIndex.enum _ i) (CopyGround.location (balls δ F s) hH e)) X := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end
