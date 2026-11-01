-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_PeriodicApproximation_GlobalCollisionLimit_positive_source_limit_q80
-- name    : OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.positive_source_limit_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:30:54.74129+00:00
-- url     : https://prove2.me/theorems/6ac3ac22-92de-4364-9ab1-5b8b55b08daf
-- title:
--   OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.positive_source_limit_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.positive_source_limit` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/PositiveContributionsIntegrable.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/PositiveContributionsIntegrable.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.PeriodicApproximation`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology`):
--
--   ```lean
--   theorem GlobalCollisionLimit.positive_source_limit_q80 {f : Density} {hfm : Measurable f}
--       (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
--       {T R L : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) (hL : 0 ≤ L) (K : ℝ≥0) :
--       Published.WeakL1Converges
--         ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
--           ((volume : Measure Velocity).restrict (Metric.closedBall 0 L))))
--         (fun n => finitePositiveSource T ((G.weakLimit.indices n:ℝ)+1) K R
--           (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
--         (physicalPositiveSource T K R G.weakLimit.kineticProfile)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.PeriodicApproximation.initialApproximation`, `OAI.BoltzmannNonuniqueness.Published.WeakL1Converges` and `OAI.BoltzmannNonuniqueness.PeriodicApproximation.BoundedCutoffSolution.kineticProfile` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.finitePositiveSource`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.physicalPositiveSource`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalWeakLimit` and `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalWeakLimit.kineticProfile` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Density`, `OAI.BoltzmannNonuniqueness.Phase`, `OAI.BoltzmannNonuniqueness.Position`, `OAI.BoltzmannNonuniqueness.Velocity` and `OAI.BoltzmannNonuniqueness.entropyMoment` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.positive_survival_lower_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/PositiveContributionsIntegrable.lean (declaration OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.positive_source_limit)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.positive_source_limit_q80 {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R L : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) (hL : 0 ≤ L) (K : ℝ≥0) :
    Published.WeakL1Converges
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 L))))
      (fun n => finitePositiveSource T ((G.weakLimit.indices n:ℝ)+1) K R
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
      (physicalPositiveSource T K R G.weakLimit.kineticProfile) := by
  sorry

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end
