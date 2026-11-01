-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_bounded_mild_entropy_dissipation_q80
-- name    : OAI.BoltzmannNonuniqueness.bounded_mild_entropy_dissipation_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:32:19.197214+00:00
-- url     : https://prove2.me/theorems/54189b9c-db59-4b74-9e70-98f361021bcc
-- title:
--   OAI.BoltzmannNonuniqueness.bounded_mild_entropy_dissipation_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.bounded_mild_entropy_dissipation` of [lean/OAI/MathematicalPhysics/Boltzmann/Branching/BoundedMildEntropyLimit.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/BoundedMildEntropyLimit.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness`, with `open MeasureTheory Set`, `open BoltzmannNonuniqueness.VelocityWeight`):
--
--   ```lean
--   theorem bounded_mild_entropy_dissipation_q80 (hcarleman : Published.GPV2009CarlemanInput)
--       {T q A δ b p : ℝ} (hT : 0 < T) (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A)
--       (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : 0 ≤ b)
--       (hp : 1 < p) (hpi : Integrable (fun v : Velocity => H q v^p))
--       {F : Evolution} {a : Density}
--       (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
--       (hFn : ∀ t z, 0 ≤ F t z) (hFb : ∀ t z, F t z ≤ A*H q z.2)
--       (ham : Measurable a) (han : ∀ z, 0 ≤ a z) (hab : ∀ z, a z ≤ A*H q z.2)
--       (hchar : (fun z : ℝ × Phase => F z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
--         (volume.restrict (Icc 0 T)).prod volume]
--           (fun z => entropyPath a (TorusFlight.along (cutoffPhysicalSource b F)) z.1 z.2))
--       (hcharT : (fun z => F T (TorusFlight.flight T z)) =ᵐ[volume]
--         entropyPath a (TorusFlight.along (cutoffPhysicalSource b F)) T) :
--       (∫ z, regularizedRelativeEntropyDensity δ (F T) z)-
--         (∫ z, regularizedRelativeEntropyDensity δ a z)+regularizedKineticDissipation T b δ F ≤
--         (δ*entropyErrorCoefficient q A b)*∫ z : (ℝ × Position) × Velocity,
--           logarithmicMajorant q (A+tiltConstant) p δ z.2
--           ∂(AnnularEnvelope.timePositionVolume T).prod volume
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.AnnularEnvelope.timePositionVolume`, `OAI.BoltzmannNonuniqueness.TorusFlight.along`, `OAI.BoltzmannNonuniqueness.TorusFlight.flight`, `OAI.BoltzmannNonuniqueness.VelocityWeight.H` and `OAI.BoltzmannNonuniqueness.VelocityWeight.tiltConstant` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.entropyPath` (definitions bundle `OAIQ080A001` of this split); `OAI.BoltzmannNonuniqueness.cutoffPhysicalSource`, `OAI.BoltzmannNonuniqueness.entropyErrorCoefficient`, `OAI.BoltzmannNonuniqueness.logarithmicMajorant`, `OAI.BoltzmannNonuniqueness.regularizedKineticDissipation`, `OAI.BoltzmannNonuniqueness.regularizedRelativeEntropyDensity` and `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Density`, `OAI.BoltzmannNonuniqueness.Evolution`, `OAI.BoltzmannNonuniqueness.Phase`, `OAI.BoltzmannNonuniqueness.Position` and `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.bounded_mild_entropy_dissipation_limit_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/BoundedMildEntropyLimit.lean (declaration OAI.BoltzmannNonuniqueness.bounded_mild_entropy_dissipation)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem bounded_mild_entropy_dissipation_q80 (hcarleman : Published.GPV2009CarlemanInput)
    {T q A δ b p : ℝ} (hT : 0 < T) (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : 0 ≤ b)
    (hp : 1 < p) (hpi : Integrable (fun v : Velocity => H q v^p))
    {F : Evolution} {a : Density}
    (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t z, 0 ≤ F t z) (hFb : ∀ t z, F t z ≤ A*H q z.2)
    (ham : Measurable a) (han : ∀ z, 0 ≤ a z) (hab : ∀ z, a z ≤ A*H q z.2)
    (hchar : (fun z : ℝ × Phase => F z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume]
        (fun z => entropyPath a (TorusFlight.along (cutoffPhysicalSource b F)) z.1 z.2))
    (hcharT : (fun z => F T (TorusFlight.flight T z)) =ᵐ[volume]
      entropyPath a (TorusFlight.along (cutoffPhysicalSource b F)) T) :
    (∫ z, regularizedRelativeEntropyDensity δ (F T) z)-
      (∫ z, regularizedRelativeEntropyDensity δ a z)+regularizedKineticDissipation T b δ F ≤
      (δ*entropyErrorCoefficient q A b)*∫ z : (ℝ × Position) × Velocity,
        logarithmicMajorant q (A+tiltConstant) p δ z.2
        ∂(AnnularEnvelope.timePositionVolume T).prod volume := by
  sorry

end BoltzmannNonuniqueness

end

end

end OAI
end
