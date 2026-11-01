-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_CollisionCompactness_DoubleGain_localizedGain_strong_of_smoothing_q80
-- name    : OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.localizedGain_strong_of_smoothing_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:17:08.523493+00:00
-- url     : https://prove2.me/theorems/c5cf272b-2954-4de1-a73d-9e7442c7f738
-- title:
--   OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.localizedGain_strong_of_smoothing_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.localizedGain_strong_of_smoothing` of [lean/OAI/MathematicalPhysics/Boltzmann/Compactness/LocalizedGainCompactness.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/LocalizedGainCompactness.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain`, with `open MeasureTheory Filter`, `open scoped ENNReal Topology`, `open Compactness PeriodicApproximation`):
--
--   ```lean
--   theorem localizedGain_strong_of_smoothing_q80
--       {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {C : ℝ}
--       (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
--       (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
--       (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
--       (hgm : Measurable g) (hg : ∀ p, 0 ≤ g p)
--       (hgi : Integrable (entropyGauge g) (μ.prod volume))
--       (η : C(Velocity,ℝ)) (hη : HasCompactSupport η)
--       {ν : Measure (X × Velocity)} (hν : ν ≤ μ.prod volume)
--       (hc : ∀ χ : C(Velocity,ℝ), HasCompactSupport χ →
--         Tendsto (fun n => eLpNorm
--           (velocitySmooth χ (localizedPhysicalGain η (f n))-
--             velocitySmooth χ (localizedPhysicalGain η g)) 1 ν) atTop (𝓝 0)) :
--       Tendsto (fun n => eLpNorm
--         (localizedPhysicalGain η (f n)-localizedPhysicalGain η g) 1 ν) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.CollisionCompactness.localizedPhysicalGain` and `OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.velocitySmooth` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.PeriodicApproximation.entropyGauge` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.normalized_gain_strong_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/LocalizedGainCompactness.lean (declaration OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.localizedGain_strong_of_smoothing)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem localizedGain_strong_of_smoothing_q80
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hgm : Measurable g) (hg : ∀ p, 0 ≤ g p)
    (hgi : Integrable (entropyGauge g) (μ.prod volume))
    (η : C(Velocity,ℝ)) (hη : HasCompactSupport η)
    {ν : Measure (X × Velocity)} (hν : ν ≤ μ.prod volume)
    (hc : ∀ χ : C(Velocity,ℝ), HasCompactSupport χ →
      Tendsto (fun n => eLpNorm
        (velocitySmooth χ (localizedPhysicalGain η (f n))-
          velocitySmooth χ (localizedPhysicalGain η g)) 1 ν) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      (localizedPhysicalGain η (f n)-localizedPhysicalGain η g) 1 ν) atTop (𝓝 0) := by
  sorry

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end OAI
end
