-- Prove2me | Theorems.Thm_OAI_FiniteFactor_sourceSamplingSquaredError_ae
-- name    : OAI.FiniteFactor.sourceSamplingSquaredError_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T23:35:59.789356+00:00
-- url     : https://prove2.me/theorems/915ca628-697a-4946-9bd4-bed1c711d277
-- title:
--   OAI.FiniteFactor.sourceSamplingSquaredError_ae: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FiniteFactor.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FiniteFactor.sourceSamplingSquaredError_ae` of [lean/OAI/Analysis/FiniteFactor/OrbitSampling/ErrorEvent.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/OrbitSampling/ErrorEvent.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FiniteFactor`, with `open MeasureTheory Filter`, `open scoped Classical Topology`):
--
--   ```lean
--   theorem sourceSamplingSquaredError_ae (r : Bool) (b : SourceCoordinate → Bool)
--       (a c a' c' : SourceCoordinate → ℝ) :
--       ∀ᵐ θ ∂sourceAngleLaw,
--         Summable (fun stage => sourceSamplingSquaredError stage r b
--           (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ) ∧
--         Tendsto (fun stage => sourceSamplingSquaredError stage r b
--           (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FiniteFactor.SourceCoordinate` and `OAI.FiniteFactor.sourceAngleLaw` (definitions bundle `OAIQ3Ff000` of this split); `OAI.FiniteFactor.sourceSamplingSquaredError` (definitions bundle `OAIQ3Ff002` of this split).
--
--   **Used by.** The proofs of `OAI.FiniteFactor.sourceSamplingLambda_rectangle_limit_event` and `OAI.FiniteFactor.sourceSamplingTrimmed_marginals_event` of this split import it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/OrbitSampling/ErrorEvent.lean (declaration OAI.FiniteFactor.sourceSamplingSquaredError_ae)

import Mathlib
import Definitions.Def_OAIQ3Ff002

section

attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical Topology
noncomputable section

theorem sourceSamplingSquaredError_ae (r : Bool) (b : SourceCoordinate → Bool)
    (a c a' c' : SourceCoordinate → ℝ) :
    ∀ᵐ θ ∂sourceAngleLaw,
      Summable (fun stage => sourceSamplingSquaredError stage r b
        (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ) ∧
      Tendsto (fun stage => sourceSamplingSquaredError stage r b
        (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ) atTop (𝓝 0) := by
  sorry

end
end FiniteFactor

end OAI
end
