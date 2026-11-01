-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_HotPairExtraction_characteristic_test_balance_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.characteristic_test_balance_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:19:17.386989+00:00
-- url     : https://prove2.me/theorems/d7d4bd2f-88d4-4b34-ba46-b969c935b196
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.characteristic_test_balance_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.characteristic_test_balance` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapLimitTransport.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapLimitTransport.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, with `open MeasureTheory Set`, `open scoped ENNReal`, `open BoltzmannNonuniqueness.TransportCutoff BoltzmannNonuniqueness.CollisionCompactness`):
--
--   ```lean
--   theorem HotPairExtraction.characteristic_test_balance_q80
--       (hDP : Published.DunfordPettis1940HotPairWindows)
--       (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
--       (E : HotPairExtraction S)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq₁ : 1 < q) (hq₂ : q < 2)
--       {a A B R Rₑ : ℝ} (ha : 0 < a) (haA : a ≤ A) (hAB : A < B)
--       (hB : ENNReal.ofReal B < E.horizon) (hR : 0 ≤ R)
--       {ψ : EuclideanFlight.CharacteristicPhase → ℝ}
--       (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
--       (hs : tsupport (EuclideanFlight.testPullback ψ) ⊆ kineticWindow a A Rₑ)
--       (hsC : ∀ z ∈ tsupport (EuclideanFlight.testPullback ψ),
--         EuclideanFlight.hotChart z ∈ coldCylinderSet a A R) :
--       (∫ z, EuclideanFlight.timeDerivative ψ
--         (EuclideanFlight.characteristicEquiv.symm (EuclideanFlight.hotChart.symm z))*E.hotLimit z
--         ∂(coldCylinderVolume a A R).prod volume)+
--         (2*(∫ z, ψ (EuclideanFlight.characteristicEquiv.symm (EuclideanFlight.hotChart.symm z))
--           ∂incomingGainMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ
--             (coldCylinderVolume a A R)))-
--         (∫ z, ψ (EuclideanFlight.characteristicEquiv.symm (EuclideanFlight.hotChart.symm z))
--           ∂incomingLossMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ
--             (coldCylinderVolume a A R)))) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.CollisionCompactness.incomingGainMeasure`, `OAI.BoltzmannNonuniqueness.CollisionCompactness.incomingLossMeasure`, `OAI.BoltzmannNonuniqueness.EuclideanFlight.CharacteristicPhase`, `OAI.BoltzmannNonuniqueness.EuclideanFlight.characteristicEquiv`, `OAI.BoltzmannNonuniqueness.EuclideanFlight.hotChart`, `OAI.BoltzmannNonuniqueness.EuclideanFlight.testPullback`, `OAI.BoltzmannNonuniqueness.EuclideanFlight.timeDerivative`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.ShrinkingCapFamily`, `OAI.BoltzmannNonuniqueness.JetPrototype.Space`, `OAI.BoltzmannNonuniqueness.Published.KineticPhase`, `OAI.BoltzmannNonuniqueness.Published.SpaceTime`, `OAI.BoltzmannNonuniqueness.Published.Velocity`, `OAI.BoltzmannNonuniqueness.VelocityWeight.Transverse`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotKineticPhase`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderSet`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotLimit` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedMeasure` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Published.DunfordPettis1940HotPairWindows`, `OAI.BoltzmannNonuniqueness.Published.GLPS1988Proposition3`, `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput` and `OAI.BoltzmannNonuniqueness.TransportCutoff.kineticWindow` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.positive_history_transfer_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.uniform_late_zero_parameters_q80` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_construction_parameters_q80` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapLimitTransport.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.characteristic_test_balance)

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

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.TransportCutoff BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.characteristic_test_balance_q80
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B R Rₑ : ℝ} (ha : 0 < a) (haA : a ≤ A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon) (hR : 0 ≤ R)
    {ψ : EuclideanFlight.CharacteristicPhase → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport (EuclideanFlight.testPullback ψ) ⊆ kineticWindow a A Rₑ)
    (hsC : ∀ z ∈ tsupport (EuclideanFlight.testPullback ψ),
      EuclideanFlight.hotChart z ∈ coldCylinderSet a A R) :
    (∫ z, EuclideanFlight.timeDerivative ψ
      (EuclideanFlight.characteristicEquiv.symm (EuclideanFlight.hotChart.symm z))*E.hotLimit z
      ∂(coldCylinderVolume a A R).prod volume)+
      (2*(∫ z, ψ (EuclideanFlight.characteristicEquiv.symm (EuclideanFlight.hotChart.symm z))
        ∂incomingGainMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ
          (coldCylinderVolume a A R)))-
      (∫ z, ψ (EuclideanFlight.characteristicEquiv.symm (EuclideanFlight.hotChart.symm z))
        ∂incomingLossMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ
          (coldCylinderVolume a A R)))) = 0 := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end
