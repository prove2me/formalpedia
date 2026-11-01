-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_cell_moment_bound_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.cell_moment_bound_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:26:12.797319+00:00
-- url     : https://prove2.me/theorems/96e25e69-b245-431b-b9ff-6ac86392e7b6
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.cell_moment_bound_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.cell_moment_bound` of [lean/OAI/MathematicalPhysics/Boltzmann/Jets/PeriodicJetFamilies.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Jets/PeriodicJetFamilies.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set`, `open scoped ENNReal`, `open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetGeometry`, `open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.VelocityMoment`):
--
--   ```lean
--   theorem cell_moment_bound_q80 {s₀ η K α γ d₀ q t Z : ℝ}
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hq : q < 2) (hZ : 0 ≤ Z)
--       (ht : 0 < t) (htmax : t ≤ 1/32)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (N : ℕ) (x : Velocity) (hx : x ∈ TorusChart.cube)
--       (F : Velocity → ℝ) (c : Label → Velocity → ℝ)
--       (hcm : ∀ i, Measurable (c i)) (hcn : ∀ i v, 0 ≤ c i v)
--       (hcs : ∀ v, Summable (fun i => c i v))
--       (hzero : ∀ i, ¬i.annulus < N → ∀ v, c i v = 0)
--       (hU : ∀ i v, H q v*c i v ≤ JetSupersolution.U η K α γ (jetScale s₀ η i.annulus)
--         (d₀*jetScale s₀ η i.annulus^10) t i.positive (JetSpatialBox.shifted x i.lattice,v))
--       (hhot : ∀ᵐ v, F v-∑' i, c i v ≤ Z) :
--       moment (fun v => H q v*F v) ≤ ENNReal.ofReal
--         ((Z+escapedConstant s₀ η K α d₀)*hotConstant q+
--           JetEnvelopeGain.momentConstant K α γ*
--             AnnularEnvelope.finiteEnvelope s₀ η (Finset.range N) t (transverse x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.AnnularEnvelope.finiteEnvelope`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.escapedConstant`, `OAI.BoltzmannNonuniqueness.JetEnvelopeGain.momentConstant`, `OAI.BoltzmannNonuniqueness.JetGeometry.jetScale`, `OAI.BoltzmannNonuniqueness.JetLattice.Label`, `OAI.BoltzmannNonuniqueness.JetPrototype.Space`, `OAI.BoltzmannNonuniqueness.JetSpatialBox.shifted`, `OAI.BoltzmannNonuniqueness.JetSupersolution.U`, `OAI.BoltzmannNonuniqueness.VelocityMoment.hotConstant`, `OAI.BoltzmannNonuniqueness.VelocityWeight.H` and `OAI.BoltzmannNonuniqueness.VelocityWeight.transverse` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.TorusChart.cube` and `OAI.BoltzmannNonuniqueness.VelocityMoment.moment` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_coldAverage_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_coldLabelAverage_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_proportional_loss_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_euclideanHotSource_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_hotSource_cylinder_integrable_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_mixedPrelimitMeasure_gaussian_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.CompactFamily.weak_limit_moment_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.cap_family_cutoff_uniformIntegrable_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.capped_family_unifTight_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CompactCapFamily.weak_limit_moment_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.cap_family_cutoff_uniformIntegrable_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_family_gainLoss_uniformIntegrable_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_family_unifTight_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_dormant_family_q80` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_tight_cap_family_at_q80` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Jets/PeriodicJetFamilies.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.cell_moment_bound)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem cell_moment_bound_q80 {s₀ η K α γ d₀ q t Z : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hq : q < 2) (hZ : 0 ≤ Z)
    (ht : 0 < t) (htmax : t ≤ 1/32)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N : ℕ) (x : Velocity) (hx : x ∈ TorusChart.cube)
    (F : Velocity → ℝ) (c : Label → Velocity → ℝ)
    (hcm : ∀ i, Measurable (c i)) (hcn : ∀ i v, 0 ≤ c i v)
    (hcs : ∀ v, Summable (fun i => c i v))
    (hzero : ∀ i, ¬i.annulus < N → ∀ v, c i v = 0)
    (hU : ∀ i v, H q v*c i v ≤ JetSupersolution.U η K α γ (jetScale s₀ η i.annulus)
      (d₀*jetScale s₀ η i.annulus^10) t i.positive (JetSpatialBox.shifted x i.lattice,v))
    (hhot : ∀ᵐ v, F v-∑' i, c i v ≤ Z) :
    moment (fun v => H q v*F v) ≤ ENNReal.ofReal
      ((Z+escapedConstant s₀ η K α d₀)*hotConstant q+
        JetEnvelopeGain.momentConstant K α γ*
          AnnularEnvelope.finiteEnvelope s₀ η (Finset.range N) t (transverse x)) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
