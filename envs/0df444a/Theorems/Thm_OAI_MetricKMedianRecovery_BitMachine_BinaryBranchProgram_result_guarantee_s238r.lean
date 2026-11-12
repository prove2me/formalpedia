-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_result_guarantee_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:25:23.891169+00:00
-- url     : https://prove2.me/theorems/71b923e1-60fe-460e-919e-494809cb1c24
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/RationalBranch.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/RationalBranch.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram`, with `open Completion Categorical FiniteSampling BinaryBranchContext`):
--
--   ```lean
--   lemma result_guarantee_s238r (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
--       (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
--       (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n) (hdel : s.deleted⊆S)
--       (colors : Fin n→Fin 3) (hH : ∀ i,(balls δ F s i).Nonempty) (hr : ∀ i,0≤ s.radius i)
--       (sel dest : Fin m→Fin n) (c k : ℕ)
--       (hinj : Function.Injective sel) (hsel : ∀ j,sel j∈(S\s.deleted).filter (fun i=>colors i=2))
--       (hdest : ∀ j,dest j∈F) (hcountDest : (Finset.univ.image dest).card ≤ c)
--       (hcount : s.leaves.length+c≤ s.deleted.card+k+m)
--       (hk : k≤((S\s.deleted).filter (fun i=>colors i=1)).card) :
--       (∀ bits,result δ D F S Δ s colors hH sel dest k bits⊆F ∧
--         (result δ D F S Δ s colors hH sel dest k bits).card=S.card ∧
--         (result δ D F S Δ s colors hH sel dest k bits).Nonempty) ∧
--       ∀ X,PartitionFeasible CopyGround.part X →
--         average (fun bits=>realCost D (result δ D F S Δ s colors hH sel dest k bits))≤
--           (38/100:ℝ)*objective δ D F S Δ s colors hH sel dest k ∅+
--           (62/100:ℝ)*objective δ D F S Δ s colors hH sel dest k X
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Categorical.BinaryOracleIndex`, `OAI.MetricKMedianRecovery.FiniteSampling.average`, `OAI.MetricKMedianRecovery.RationalSampling.State`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.balls`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.objective`, `OAI.MetricKMedianRecovery.Categorical.Explicit.exponent`, `OAI.MetricKMedianRecovery.Categorical.Explicit.samples` and `OAI.MetricKMedianRecovery.Completion.CopyGround.part` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Categorical.PartitionFeasible` and `OAI.MetricKMedianRecovery.Completion.realCost` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq` and `OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype` (definitions bundle `Q238L010` of this split); `OAI.MetricKMedianRecovery.RationalSampling.State.radius` (definitions bundle `Q238L011` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.planned_successful_completion_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.amplified_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.successful_probability_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.result_success_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.fair_zero_completion_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.successful_completion_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/RationalBranch.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee)

import Mathlib
import Definitions.Def_Q238L008
import Definitions.Def_Q238L010
import Definitions.Def_Q238L011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext
variable {n m : ℕ}
variable [PseudoMetricSpace (Fin n)]
lemma result_guarantee_s238r (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
    (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n) (hdel : s.deleted⊆S)
    (colors : Fin n→Fin 3) (hH : ∀ i,(balls δ F s i).Nonempty) (hr : ∀ i,0≤ s.radius i)
    (sel dest : Fin m→Fin n) (c k : ℕ)
    (hinj : Function.Injective sel) (hsel : ∀ j,sel j∈(S\s.deleted).filter (fun i=>colors i=2))
    (hdest : ∀ j,dest j∈F) (hcountDest : (Finset.univ.image dest).card ≤ c)
    (hcount : s.leaves.length+c≤ s.deleted.card+k+m)
    (hk : k≤((S\s.deleted).filter (fun i=>colors i=1)).card) :
    (∀ bits,result δ D F S Δ s colors hH sel dest k bits⊆F ∧
      (result δ D F S Δ s colors hH sel dest k bits).card=S.card ∧
      (result δ D F S Δ s colors hH sel dest k bits).Nonempty) ∧
    ∀ X,PartitionFeasible CopyGround.part X →
      average (fun bits=>realCost D (result δ D F S Δ s colors hH sel dest k bits))≤
        (38/100:ℝ)*objective δ D F S Δ s colors hH sel dest k ∅+
        (62/100:ℝ)*objective δ D F S Δ s colors hH sel dest k X := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end
