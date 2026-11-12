-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_planned_successful_completion_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.planned_successful_completion_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:34:11.129118+00:00
-- url     : https://prove2.me/theorems/6875d0da-7d1d-4408-8389-e5bbcd814b8e
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.planned_successful_completion_s238r (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.planned_successful_completion` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/CopyComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CopyComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram`, with `open Completion Categorical FiniteSampling BinaryBranchContext Sampling`):
--
--   ```lean
--   lemma planned_successful_completion_s238r
--       (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
--       (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
--       (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
--       (Δ : ℚ) (hΔ : 0≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
--       (s : RationalSampling.State n) (hs : C.Correct hD (1/1000000) s.real)
--       (hP : 0 < comparisonCost D C.assign) (hm : 0<C.bad.card)
--       (hI : C.removalTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
--       (hN : C.nearTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
--       (colors : Fin n→Fin 3)
--       (hcolors : ∀ u∈(C.nonproxy\s.real.deleted)∪designatedProxies (C.nonproxy\s.real.deleted)
--         (C.designatedDestination hD s.real (19/50)),colors u=requiredColors (C.nonproxy\s.real.deleted)
--         (C.designatedDestination hD s.real (19/50)) u)
--       (label : Fin n→Fin m)
--       (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=m)
--       (P : BlueSubsetDP.Plan ((S\s.deleted).filter (fun i=>colors i=2)) F label
--         (fun u v=>(rationalScore δ D S Δ s u v:ℝ))
--         (((designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).image
--           (C.blueDestination hD s.real (19/50))).card))
--       (hvalue : (∑ l,branchScore D S (Δ:ℝ) s.real (P.sel l) (P.dst l))≤
--         ∑ u∈designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50)),
--           assignmentWeight D (completionAssignment S (Δ:ℝ) s.real) u*
--             minimumMixed (19/50) (C.coveredCenter s.real) (leafCenter s.real) (leafRadius s.real)
--               (C.destinations s.real) (C.destinations_nonempty hD s.real) u) :
--       ∃ hH : ∀ i,(balls δ F s i).Nonempty,
--         (∀ bits,result δ D F S Δ s colors hH P.sel P.dst
--             (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits⊆F ∧
--           (result δ D F S Δ s colors hH P.sel P.dst
--             (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits).card=S.card ∧
--           (result δ D F S Δ s colors hH P.sel P.dst
--             (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits).Nonempty) ∧
--         average (fun bits=>realCost D (result δ D F S Δ s colors hH P.sel P.dst
--           (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits))≤
--             (240258179/125000000:ℝ)*comparisonCost D C.assign
--   ```
--
--   **Definitions.** The statement is written with `OAI.BlueSubsetDP.Plan` (definitions bundle `Q238L000` of this split); `OAI.MetricKMedianRecovery.Categorical.BinaryOracleIndex`, `OAI.MetricKMedianRecovery.FiniteSampling.average`, `OAI.MetricKMedianRecovery.RationalSampling.State`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.balls`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.rationalScore`, `OAI.MetricKMedianRecovery.Categorical.Explicit.exponent`, `OAI.MetricKMedianRecovery.Categorical.Explicit.samples`, `OAI.MetricKMedianRecovery.RationalSampling.State.real` and `OAI.MetricKMedianRecovery.Sampling.State` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Completion.assignmentWeight`, `OAI.MetricKMedianRecovery.Completion.designatedBlue`, `OAI.MetricKMedianRecovery.Completion.designatedProxies`, `OAI.MetricKMedianRecovery.Completion.designatedRed`, `OAI.MetricKMedianRecovery.Completion.minimumMixed`, `OAI.MetricKMedianRecovery.Completion.realCost`, `OAI.MetricKMedianRecovery.Completion.requiredColors`, `OAI.MetricKMedianRecovery.Sampling.Comparison` and `OAI.MetricKMedianRecovery.Sampling.comparisonCost` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq` and `OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype` (definitions bundle `Q238L010` of this split); `OAI.MetricKMedianRecovery.Sampling.completionAssignment`, `OAI.MetricKMedianRecovery.Sampling.leafCenter`, `OAI.MetricKMedianRecovery.Sampling.leafRadius`, `OAI.MetricKMedianRecovery.Sampling.Comparison.Correct`, `OAI.MetricKMedianRecovery.Sampling.Comparison.bad`, `OAI.MetricKMedianRecovery.Sampling.Comparison.blueDestination`, `OAI.MetricKMedianRecovery.Sampling.Comparison.coveredCenter`, `OAI.MetricKMedianRecovery.Sampling.Comparison.designatedDestination`, `OAI.MetricKMedianRecovery.Sampling.Comparison.destinations`, `OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_nonempty`, `OAI.MetricKMedianRecovery.Sampling.Comparison.nearTotal`, `OAI.MetricKMedianRecovery.Sampling.Comparison.nonproxy` and `OAI.MetricKMedianRecovery.Sampling.Comparison.removalTotal` (definitions bundle `Q238L011` of this split); `OAI.MetricKMedianRecovery.Sampling.branchScore` (definitions bundle `Q238L021` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.successful_probability_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CopyComparison.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.planned_successful_completion)

import Mathlib
import Definitions.Def_Q238L008
import Definitions.Def_Q238L021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext Sampling
variable {n m : ℕ} [PseudoMetricSpace (Fin n)]
lemma planned_successful_completion_s238r
    (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
    (Δ : ℚ) (hΔ : 0≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (s : RationalSampling.State n) (hs : C.Correct hD (1/1000000) s.real)
    (hP : 0 < comparisonCost D C.assign) (hm : 0<C.bad.card)
    (hI : C.removalTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (colors : Fin n→Fin 3)
    (hcolors : ∀ u∈(C.nonproxy\s.real.deleted)∪designatedProxies (C.nonproxy\s.real.deleted)
      (C.designatedDestination hD s.real (19/50)),colors u=requiredColors (C.nonproxy\s.real.deleted)
      (C.designatedDestination hD s.real (19/50)) u)
    (label : Fin n→Fin m)
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=m)
    (P : BlueSubsetDP.Plan ((S\s.deleted).filter (fun i=>colors i=2)) F label
      (fun u v=>(rationalScore δ D S Δ s u v:ℝ))
      (((designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).image
        (C.blueDestination hD s.real (19/50))).card))
    (hvalue : (∑ l,branchScore D S (Δ:ℝ) s.real (P.sel l) (P.dst l))≤
      ∑ u∈designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50)),
        assignmentWeight D (completionAssignment S (Δ:ℝ) s.real) u*
          minimumMixed (19/50) (C.coveredCenter s.real) (leafCenter s.real) (leafRadius s.real)
            (C.destinations s.real) (C.destinations_nonempty hD s.real) u) :
    ∃ hH : ∀ i,(balls δ F s i).Nonempty,
      (∀ bits,result δ D F S Δ s colors hH P.sel P.dst
          (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits⊆F ∧
        (result δ D F S Δ s colors hH P.sel P.dst
          (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits).card=S.card ∧
        (result δ D F S Δ s colors hH P.sel P.dst
          (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits).Nonempty) ∧
      average (fun bits=>realCost D (result δ D F S Δ s colors hH P.sel P.dst
        (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits))≤
          (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end
