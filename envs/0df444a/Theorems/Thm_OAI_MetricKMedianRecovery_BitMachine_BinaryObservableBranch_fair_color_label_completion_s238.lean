-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryObservableBranch_fair_color_label_completion_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.fair_color_label_completion_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:42:03.326975+00:00
-- url     : https://prove2.me/theorems/57efdc45-4d2c-4ecc-b8d4-9d5276ef3ddc
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.fair_color_label_completion_s238 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.fair_color_label_completion` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/FavorableReady.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/FavorableReady.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch`, with `open Completion Categorical FiniteSampling BinaryBranchContext Sampling BinaryBranchProgram`):
--
--   ```lean
--   lemma fair_color_label_completion_s238
--       (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
--       (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
--       (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
--       (Δ : ℚ) (hΔ : 0≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
--       (s : RationalSampling.State n) (hs : C.Correct hD (1/1000000) s.real)
--       (hP : 0 < comparisonCost D C.assign) (hm : 0<C.bad.card)
--       (hI : C.removalTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
--       (hN : C.nearTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
--       (b : ℕ) (hb : 0<b)
--       (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=b)
--       (r0 y0 : Fin n) :
--       let q:=(designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card
--       let c:=((designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).image
--         (C.blueDestination hD s.real (19/50))).card
--       (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)≤
--         probability (fun seed : ((Fin n→Fin 4) × (Fin n→Fin (ColorLabel.labelRange b))) × Bits n s.leaves.length=>
--           realCost D (output δ D F S Δ s (fun u=>ColorLabel.color (seed.1.1 u))
--             (fun u=>ColorLabel.label b hb (seed.1.2 u)) q c r0 y0 seed.2)≤
--               (197/100:ℝ)*comparisonCost D C.assign)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Categorical.BinaryOracleIndex`, `OAI.MetricKMedianRecovery.FiniteSampling.probability`, `OAI.MetricKMedianRecovery.RationalSampling.State`, `OAI.MetricKMedianRecovery.Categorical.Explicit.exponent`, `OAI.MetricKMedianRecovery.Categorical.Explicit.samples`, `OAI.MetricKMedianRecovery.RationalSampling.State.real` and `OAI.MetricKMedianRecovery.Sampling.State` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.ColorLabel.color`, `OAI.MetricKMedianRecovery.ColorLabel.label` and `OAI.MetricKMedianRecovery.ColorLabel.labelRange` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.Completion.designatedBlue`, `OAI.MetricKMedianRecovery.Completion.designatedRed`, `OAI.MetricKMedianRecovery.Completion.realCost`, `OAI.MetricKMedianRecovery.Sampling.Comparison` and `OAI.MetricKMedianRecovery.Sampling.comparisonCost` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq` and `OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.bad` and `OAI.MetricKMedianRecovery.Sampling.Comparison.nonproxy` (definitions bundle `Q238K015` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.Bits` and `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.output` (definitions bundle `Q238K020` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.Correct`, `OAI.MetricKMedianRecovery.Sampling.Comparison.nearTotal` and `OAI.MetricKMedianRecovery.Sampling.Comparison.removalTotal` (definitions bundle `Q238K022` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.blueDestination` and `OAI.MetricKMedianRecovery.Sampling.Comparison.designatedDestination` (definitions bundle `Q238K027` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.result_success_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/FavorableReady.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.fair_color_label_completion)

import Mathlib
import Definitions.Def_Q238K027

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open Completion Categorical FiniteSampling BinaryBranchContext Sampling BinaryBranchProgram
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma fair_color_label_completion_s238
    (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
    (Δ : ℚ) (hΔ : 0≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (s : RationalSampling.State n) (hs : C.Correct hD (1/1000000) s.real)
    (hP : 0 < comparisonCost D C.assign) (hm : 0<C.bad.card)
    (hI : C.removalTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (b : ℕ) (hb : 0<b)
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=b)
    (r0 y0 : Fin n) :
    let q:=(designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card
    let c:=((designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).image
      (C.blueDestination hD s.real (19/50))).card
    (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)≤
      probability (fun seed : ((Fin n→Fin 4) × (Fin n→Fin (ColorLabel.labelRange b))) × Bits n s.leaves.length=>
        realCost D (output δ D F S Δ s (fun u=>ColorLabel.color (seed.1.1 u))
          (fun u=>ColorLabel.label b hb (seed.1.2 u)) q c r0 y0 seed.2)≤
            (197/100:ℝ)*comparisonCost D C.assign) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

end OAI
end
