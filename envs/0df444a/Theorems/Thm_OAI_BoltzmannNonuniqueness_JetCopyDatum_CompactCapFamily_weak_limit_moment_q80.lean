-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_CompactCapFamily_weak_limit_moment_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.CompactCapFamily.weak_limit_moment_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:24:21.878998+00:00
-- url     : https://prove2.me/theorems/6388bd33-e768-46ef-8792-57191ad564f7
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.CompactCapFamily.weak_limit_moment_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.CompactCapFamily.weak_limit_moment` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapHotTransportBalance.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapHotTransportBalance.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory`, `open scoped ENNReal`, `open BoltzmannNonuniqueness.WeightedLocalControl`):
--
--   ```lean
--   theorem CompactCapFamily.weak_limit_moment_q80 {s₀ η K α γ d₀ q : ℝ}
--       (F : CompactCapFamily s₀ η K α γ d₀ q)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq : q < 2)
--       {φ : ℕ → ℕ} {g : (ℝ × Position) × Velocity → ℝ}
--       (hg : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
--         (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g)
--       (hgn : ∀ p, 0 ≤ g p) :
--       ∀ᵐ u ∂AnnularEnvelope.timePositionVolume F.time,
--         VelocityMoment.moment (fun v => g (u,v)) ≤
--           ENNReal.ofReal (AnnularEnvelope.commonMoment s₀ η
--             (momentBase s₀ η K α d₀ q) (JetEnvelopeGain.momentConstant K α γ)
--             (AnnularEnvelope.torusChart u))
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.AnnularEnvelope.commonMoment`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.timePositionVolume`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.torusChart`, `OAI.BoltzmannNonuniqueness.DatumBounds.scale`, `OAI.BoltzmannNonuniqueness.HotSeedProfile.normalized`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CompactCapFamily`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.initial`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.momentBase`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.torusPhysical`, `OAI.BoltzmannNonuniqueness.JetEnvelopeGain.momentConstant`, `OAI.BoltzmannNonuniqueness.JetPrototype.Phase`, `OAI.BoltzmannNonuniqueness.Published.WeakL1Converges`, `OAI.BoltzmannNonuniqueness.WeightedLocalControl.damping`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation` and `OAI.BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.VelocityMoment.moment` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Position` and `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_limit_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapHotTransportBalance.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.CompactCapFamily.weak_limit_moment)

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

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CompactCapFamily.weak_limit_moment_q80 {s₀ η K α γ d₀ q : ℝ}
    (F : CompactCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq : q < 2)
    {φ : ℕ → ℕ} {g : (ℝ × Position) × Velocity → ℝ}
    (hg : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
      (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g)
    (hgn : ∀ p, 0 ≤ g p) :
    ∀ᵐ u ∂AnnularEnvelope.timePositionVolume F.time,
      VelocityMoment.moment (fun v => g (u,v)) ≤
        ENNReal.ofReal (AnnularEnvelope.commonMoment s₀ η
          (momentBase s₀ η K α d₀ q) (JetEnvelopeGain.momentConstant K α γ)
          (AnnularEnvelope.torusChart u)) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
