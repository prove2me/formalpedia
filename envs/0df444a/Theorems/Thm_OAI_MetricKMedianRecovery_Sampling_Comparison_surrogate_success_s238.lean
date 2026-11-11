-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Sampling_Comparison_surrogate_success_s238
-- name    : OAI.MetricKMedianRecovery.Sampling.Comparison.surrogate_success_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:33:28.894042+00:00
-- url     : https://prove2.me/theorems/cd8a53d1-ccac-4db0-ae22-4d1e8a825362
-- title:
--   OAI.MetricKMedianRecovery.Sampling.Comparison.surrogate_success_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Sampling.Comparison.surrogate_success` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/Destinations.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Destinations.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Sampling.Comparison`, with `open Completion`):
--
--   ```lean
--   lemma surrogate_success_s238 {E R : Type*} [DecidableEq E] [Fintype R]
--       (C : Comparison D S O) (hD : D.Nonempty)
--       (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
--       (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
--       (hI : C.removalTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
--       (hN : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
--       (loc : E → V) (X : Finset E)
--       (hcenter : ∀ i, ∃ e ∈ X, loc e = C.coveredCenter s i)
--       (G Blue : Finset V) (redLoc : R → V) (hredInj : Function.Injective redLoc)
--       (q : ℕ) (T : Finset R) (hT : T.card = q)
--       (hdisj : Disjoint (T.image redLoc) Blue)
--       (hcover : T.image redLoc ∪ Blue = C.nonproxy \ s.deleted)
--       (hredDest : ∀ r ∈ T,
--         match selectedDestination (19/50) (C.coveredCenter s) (leafCenter s) (leafRadius s)
--             (C.destinations s) (C.destinations_nonempty hD s) (redLoc r) with
--         | .proxy φ => φ ∈ G | .covered _ => True | .uncovered _ => False)
--       (K : ℝ)
--       (hK : K ≤ ∑ u ∈ Blue, assignmentWeight D (completionAssignment S Δ s) u *
--         minimumMixed (19/50) (C.coveredCenter s) (leafCenter s) (leafRadius s)
--           (C.destinations s) (C.destinations_nonempty hD s) u) :
--       let Ψ := surrogate (P := ↥D) K q
--         (fun p => virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p)
--         (fun p e => dist (p:V) (loc e))
--         (fun r => assignmentWeight D (completionAssignment S Δ s) (redLoc r))
--         (fun r => virtualNearest G (leafCenter s) (leafRadius s) Δ (redLoc r))
--         (fun r e => dist (redLoc r) (loc e))
--       (19/50)*Ψ ∅+(1-19/50)*Ψ X ≤
--         (240258179/125000000:ℝ)*comparisonCost D C.assign
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Completion.surrogate` and `OAI.MetricKMedianRecovery.Sampling.State` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Completion.Destination`, `OAI.MetricKMedianRecovery.Completion.assignmentWeight`, `OAI.MetricKMedianRecovery.Completion.minimumMixed`, `OAI.MetricKMedianRecovery.Completion.selectedDestination`, `OAI.MetricKMedianRecovery.Completion.virtualNearest`, `OAI.MetricKMedianRecovery.Sampling.Comparison` and `OAI.MetricKMedianRecovery.Sampling.comparisonCost` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.Sampling.completionAssignment`, `OAI.MetricKMedianRecovery.Sampling.Comparison.bad` and `OAI.MetricKMedianRecovery.Sampling.Comparison.nonproxy` (definitions bundle `Q238K015` of this split); `OAI.MetricKMedianRecovery.Sampling.leafCenter`, `OAI.MetricKMedianRecovery.Sampling.leafRadius` and `OAI.MetricKMedianRecovery.Sampling.Comparison.coveredCenter` (definitions bundle `Q238K016` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.Correct`, `OAI.MetricKMedianRecovery.Sampling.Comparison.destinations`, `OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_nonempty`, `OAI.MetricKMedianRecovery.Sampling.Comparison.nearTotal` and `OAI.MetricKMedianRecovery.Sampling.Comparison.removalTotal` (definitions bundle `Q238K022` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.planned_successful_completion_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.successful_completion_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryZeroBranch_successful_probability_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Destinations.lean (declaration OAI.MetricKMedianRecovery.Sampling.Comparison.surrogate_success)

import Mathlib
import Definitions.Def_Q238K022

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

lemma surrogate_success_s238 {E R : Type*} [DecidableEq E] [Fintype R]
    (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (hI : C.removalTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (loc : E → V) (X : Finset E)
    (hcenter : ∀ i, ∃ e ∈ X, loc e = C.coveredCenter s i)
    (G Blue : Finset V) (redLoc : R → V) (hredInj : Function.Injective redLoc)
    (q : ℕ) (T : Finset R) (hT : T.card = q)
    (hdisj : Disjoint (T.image redLoc) Blue)
    (hcover : T.image redLoc ∪ Blue = C.nonproxy \ s.deleted)
    (hredDest : ∀ r ∈ T,
      match selectedDestination (19/50) (C.coveredCenter s) (leafCenter s) (leafRadius s)
          (C.destinations s) (C.destinations_nonempty hD s) (redLoc r) with
      | .proxy φ => φ ∈ G | .covered _ => True | .uncovered _ => False)
    (K : ℝ)
    (hK : K ≤ ∑ u ∈ Blue, assignmentWeight D (completionAssignment S Δ s) u *
      minimumMixed (19/50) (C.coveredCenter s) (leafCenter s) (leafRadius s)
        (C.destinations s) (C.destinations_nonempty hD s) u) :
    let Ψ := surrogate (P := ↥D) K q
      (fun p => virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p)
      (fun p e => dist (p:V) (loc e))
      (fun r => assignmentWeight D (completionAssignment S Δ s) (redLoc r))
      (fun r => virtualNearest G (leafCenter s) (leafRadius s) Δ (redLoc r))
      (fun r e => dist (redLoc r) (loc e))
    (19/50)*Ψ ∅+(1-19/50)*Ψ X ≤
      (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  sorry

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end
