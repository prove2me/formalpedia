-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_bounded_mild_entropy_dissipation_limit_q80
-- name    : OAI.BoltzmannNonuniqueness.bounded_mild_entropy_dissipation_limit_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:32:21.070987+00:00
-- url     : https://prove2.me/theorems/cd78c46c-4aaa-411f-91a6-8deb19f9ce0e
-- title:
--   OAI.BoltzmannNonuniqueness.bounded_mild_entropy_dissipation_limit_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.bounded_mild_entropy_dissipation_limit` of [lean/OAI/MathematicalPhysics/Boltzmann/Branching/BoundedMildEntropyLimit.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/BoundedMildEntropyLimit.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology`, `open BoltzmannNonuniqueness.VelocityWeight`):
--
--   ```lean
--   theorem bounded_mild_entropy_dissipation_limit_q80 (hcarleman : Published.GPV2009CarlemanInput)
--       {q b R T : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 < T)
--       {E : Evolution} {a : Density}
--       (hEm : Measurable (fun z : ℝ × Phase => E z.1 z.2))
--       (hEn : ∀ t z, 0 ≤ E t z) (hEb : ∀ t z, E t z ≤ R*H q z.2)
--       (ham : Measurable a) (han : ∀ z, 0 ≤ a z) (hab : ∀ z, a z ≤ R*H q z.2)
--       (hc : (fun z : ℝ × Phase => E z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
--         (volume.restrict (Icc 0 T)).prod volume]
--         (fun z => entropyPath a (TorusFlight.along (cutoffPhysicalSource b E)) z.1 z.2))
--       (hcT : (fun z => E T (TorusFlight.flight T z)) =ᵐ[volume]
--         entropyPath a (TorusFlight.along (cutoffPhysicalSource b E)) T) :
--       ENNReal.ofReal (relativeEntropy (E T))+
--         CollisionCompactness.cutoffExtendedDissipation (AnnularEnvelope.timePositionVolume T) b
--           (kineticDensity E) ≤ ENNReal.ofReal (relativeEntropy a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.kineticDensity`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.timePositionVolume`, `OAI.BoltzmannNonuniqueness.CollisionCompactness.cutoffExtendedDissipation`, `OAI.BoltzmannNonuniqueness.TorusFlight.along`, `OAI.BoltzmannNonuniqueness.TorusFlight.flight` and `OAI.BoltzmannNonuniqueness.VelocityWeight.H` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.entropyPath` (definitions bundle `OAIQ080A001` of this split); `OAI.BoltzmannNonuniqueness.cutoffPhysicalSource` and `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Density`, `OAI.BoltzmannNonuniqueness.Evolution`, `OAI.BoltzmannNonuniqueness.Phase`, `OAI.BoltzmannNonuniqueness.Position`, `OAI.BoltzmannNonuniqueness.Velocity` and `OAI.BoltzmannNonuniqueness.relativeEntropy` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.TightFamily.entropy_mild_limit_of_convergence_q80` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.entropy_mild_limit_of_convergence_q80` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/BoundedMildEntropyLimit.lean (declaration OAI.BoltzmannNonuniqueness.bounded_mild_entropy_dissipation_limit)

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

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem bounded_mild_entropy_dissipation_limit_q80 (hcarleman : Published.GPV2009CarlemanInput)
    {q b R T : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 < T)
    {E : Evolution} {a : Density}
    (hEm : Measurable (fun z : ℝ × Phase => E z.1 z.2))
    (hEn : ∀ t z, 0 ≤ E t z) (hEb : ∀ t z, E t z ≤ R*H q z.2)
    (ham : Measurable a) (han : ∀ z, 0 ≤ a z) (hab : ∀ z, a z ≤ R*H q z.2)
    (hc : (fun z : ℝ × Phase => E z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume]
      (fun z => entropyPath a (TorusFlight.along (cutoffPhysicalSource b E)) z.1 z.2))
    (hcT : (fun z => E T (TorusFlight.flight T z)) =ᵐ[volume]
      entropyPath a (TorusFlight.along (cutoffPhysicalSource b E)) T) :
    ENNReal.ofReal (relativeEntropy (E T))+
      CollisionCompactness.cutoffExtendedDissipation (AnnularEnvelope.timePositionVolume T) b
        (kineticDensity E) ≤ ENNReal.ofReal (relativeEntropy a) := by
  sorry

end BoltzmannNonuniqueness

end

end

end OAI
end
