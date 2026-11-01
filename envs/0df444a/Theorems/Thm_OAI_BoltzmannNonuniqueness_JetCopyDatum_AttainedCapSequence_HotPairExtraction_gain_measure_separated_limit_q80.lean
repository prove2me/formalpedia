-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_HotPairExtraction_gain_measure_separated_limit_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.gain_measure_separated_limit_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:20:56.13014+00:00
-- url     : https://prove2.me/theorems/b9e9f7c3-230c-4c5a-9a2b-5a77d3fcdfa2
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.gain_measure_separated_limit_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.gain_measure_separated_limit` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapLimitTransport.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapLimitTransport.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology`, `open BoltzmannNonuniqueness.CollisionCompactness`):
--
--   ```lean
--   theorem HotPairExtraction.gain_measure_separated_limit_q80
--       (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
--       (E : HotPairExtraction S)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq₁ : 1 < q) (hq₂ : q < 2) {a A R : ℝ}
--       (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < E.horizon) (hR : 0 ≤ R)
--       {B : ℝ} {θ : ℝ × JetPrototype.Space → ℝ} (hθ : Measurable θ) (hθB : ∀ x, |θ x| ≤ B)
--       {φ : Velocity → ℝ} (hφ : Continuous φ) {C : ℝ} (hφC : ∀ v, |φ v| ≤ C) :
--       Tendsto (fun n => ∫ z, θ z.1*φ z.2 ∂S.physicalGainMeasure a A R (E.indices n)) atTop
--         (𝓝 (∫ z, θ z.1*φ z.2 ∂incomingGainMeasure
--           (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.CollisionCompactness.incomingGainMeasure`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.ShrinkingCapFamily`, `OAI.BoltzmannNonuniqueness.JetPrototype.Space`, `OAI.BoltzmannNonuniqueness.VelocityWeight.Transverse`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotKineticPhase`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.physicalGainMeasure`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedMeasure` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Published.GLPS1988Proposition3` and `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.characteristic_test_balance_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapLimitTransport.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.gain_measure_separated_limit)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.gain_measure_separated_limit_q80
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {a A R : ℝ}
    (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < E.horizon) (hR : 0 ≤ R)
    {B : ℝ} {θ : ℝ × JetPrototype.Space → ℝ} (hθ : Measurable θ) (hθB : ∀ x, |θ x| ≤ B)
    {φ : Velocity → ℝ} (hφ : Continuous φ) {C : ℝ} (hφC : ∀ v, |φ v| ≤ C) :
    Tendsto (fun n => ∫ z, θ z.1*φ z.2 ∂S.physicalGainMeasure a A R (E.indices n)) atTop
      (𝓝 (∫ z, θ z.1*φ z.2 ∂incomingGainMeasure
        (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end
