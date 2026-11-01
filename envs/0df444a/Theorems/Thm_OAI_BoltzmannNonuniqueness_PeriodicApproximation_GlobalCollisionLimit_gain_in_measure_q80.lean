-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_PeriodicApproximation_GlobalCollisionLimit_gain_in_measure_q80
-- name    : OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.gain_in_measure_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:29:21.167079+00:00
-- url     : https://prove2.me/theorems/e46c0517-d792-4884-879b-139fae705e38
-- title:
--   OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.gain_in_measure_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.gain_in_measure` of [lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PeriodicCharacteristicGainUnit.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PeriodicCharacteristicGainUnit.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.PeriodicApproximation`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology`, `open Compactness CollisionCompactness`):
--
--   ```lean
--   theorem GlobalCollisionLimit.gain_in_measure_q80 {f : Density} {hfm : Measurable f}
--       (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
--       {T : ℝ} (hT : 0 ≤ T) (R : ℝ) :
--       TendstoInMeasure
--         (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
--           ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))
--         (fun n => gain ((G.weakLimit.indices n:ℝ)+1)
--           (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
--         atTop (gainDensity G.weakLimit.kineticProfile)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.CollisionCompactness.gainDensity`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.gain`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.initialApproximation` and `OAI.BoltzmannNonuniqueness.PeriodicApproximation.BoundedCutoffSolution.kineticProfile` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalWeakLimit` and `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalWeakLimit.kineticProfile` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Density`, `OAI.BoltzmannNonuniqueness.Phase`, `OAI.BoltzmannNonuniqueness.Position`, `OAI.BoltzmannNonuniqueness.Velocity` and `OAI.BoltzmannNonuniqueness.entropyMoment` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.gain_discrepancy_L1_q80` and `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.linear_gain_discrepancy_L1_q80` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PeriodicCharacteristicGainUnit.lean (declaration OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.gain_in_measure)

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
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness

theorem GlobalCollisionLimit.gain_in_measure_q80 {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (R : ℝ) :
    TendstoInMeasure
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))
      (fun n => gain ((G.weakLimit.indices n:ℝ)+1)
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
      atTop (gainDensity G.weakLimit.kineticProfile) := by
  sorry

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end
