-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryZeroBranch_successful_completion_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.successful_completion_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:38:08.383309+00:00
-- url     : https://prove2.me/theorems/f177fe32-637f-4639-a7ba-441b4f54c2b2
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.successful_completion_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.successful_completion` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/DesignatedBranchSuccess.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/DesignatedBranchSuccess.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch`, with `open Completion Categorical FiniteSampling BinaryBranchContext Sampling BinaryBranchProgram`):
--
--   ```lean
--   lemma successful_completion_s238r
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
--       (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=0) :
--       let q:=(designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card
--       average (fun bits=>realCost D (output δ D F S Δ s colors q bits))≤
--         (240258179/125000000:ℝ)*comparisonCost D C.assign
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Categorical.BinaryOracleIndex`, `OAI.MetricKMedianRecovery.FiniteSampling.average`, `OAI.MetricKMedianRecovery.RationalSampling.State`, `OAI.MetricKMedianRecovery.Categorical.Explicit.exponent`, `OAI.MetricKMedianRecovery.Categorical.Explicit.samples`, `OAI.MetricKMedianRecovery.RationalSampling.State.real` and `OAI.MetricKMedianRecovery.Sampling.State` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Completion.designatedBlue`, `OAI.MetricKMedianRecovery.Completion.designatedProxies`, `OAI.MetricKMedianRecovery.Completion.designatedRed`, `OAI.MetricKMedianRecovery.Completion.realCost`, `OAI.MetricKMedianRecovery.Completion.requiredColors`, `OAI.MetricKMedianRecovery.Sampling.Comparison` and `OAI.MetricKMedianRecovery.Sampling.comparisonCost` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq` and `OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype` (definitions bundle `Q238L010` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.Correct`, `OAI.MetricKMedianRecovery.Sampling.Comparison.bad`, `OAI.MetricKMedianRecovery.Sampling.Comparison.designatedDestination`, `OAI.MetricKMedianRecovery.Sampling.Comparison.nearTotal`, `OAI.MetricKMedianRecovery.Sampling.Comparison.nonproxy` and `OAI.MetricKMedianRecovery.Sampling.Comparison.removalTotal` (definitions bundle `Q238L011` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.output` (definitions bundle `Q238L026` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.fair_zero_completion_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/DesignatedBranchSuccess.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.successful_completion)

import Mathlib
import Definitions.Def_Q238L026

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryZeroBranch
open Completion Categorical FiniteSampling BinaryBranchContext Sampling BinaryBranchProgram
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma successful_completion_s238r
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
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=0) :
    let q:=(designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card
    average (fun bits=>realCost D (output δ D F S Δ s colors q bits))≤
      (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

end OAI
end
