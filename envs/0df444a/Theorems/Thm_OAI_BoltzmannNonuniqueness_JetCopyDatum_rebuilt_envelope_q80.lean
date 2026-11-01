-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_rebuilt_envelope_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.rebuilt_envelope_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:27:46.745009+00:00
-- url     : https://prove2.me/theorems/32a90a1c-0ac3-4483-9646-4eab73b04f51
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.rebuilt_envelope_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.rebuilt_envelope` of [lean/OAI/MathematicalPhysics/Boltzmann/Jets/JetFamilyBounds.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Jets/JetFamilyBounds.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set`, `open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation`):
--
--   ```lean
--   theorem rebuilt_envelope_q80 {s₀ η K α γ d₀ q b L T R : ℝ}
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hTmax : T ≤ 1)
--       (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
--       (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
--       {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
--       (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
--       (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
--       (i : JetLattice.Label) {t : ℝ} (ht : t ∈ Ioc 0 T) (p : JetPrototype.Phase) :
--       physical q (rebuilt s₀ η K α γ d₀ q b L T N F i) (t,p) ≤
--         JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
--           (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
--           (shift (displacement i.lattice) p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.CutoffLipschitz.frequencyConstant`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.displacement`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.initial`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.rebuilt`, `OAI.BoltzmannNonuniqueness.JetGeometry.jetScale`, `OAI.BoltzmannNonuniqueness.JetLattice.Label`, `OAI.BoltzmannNonuniqueness.JetPrototype.Phase`, `OAI.BoltzmannNonuniqueness.JetPrototype.Space`, `OAI.BoltzmannNonuniqueness.JetSupersolution.U`, `OAI.BoltzmannNonuniqueness.VelocityWeight.Transverse` and `OAI.BoltzmannNonuniqueness.WeightedTranslation.shift` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.WeightedLocal.physical` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.coldLabel_average_free_L1_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.cold_mesh_average_L1_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_coldAverage_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_coldLabelAverage_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_proportional_loss_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_euclideanHotSource_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_hotSource_cylinder_integrable_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_mixedPrelimitMeasure_gaussian_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.CompactFamily.weak_limit_moment_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.cap_family_cutoff_uniformIntegrable_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.capped_family_unifTight_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.cold_source_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.escapedTotal_bound_global_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.hot_net_source_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.rescaled_cold_measure_majorant_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CompactCapFamily.weak_limit_moment_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.DormantLimit.central_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.cap_family_cutoff_uniformIntegrable_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_family_gainLoss_uniformIntegrable_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_family_unifTight_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_spacetime_outer_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_total_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_dormant_approximation_family_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_dormant_family_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_tight_cap_family_at_q80` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_zero_solution_large_q80` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Jets/JetFamilyBounds.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.rebuilt_envelope)

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
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem rebuilt_envelope_q80 {s₀ η K α γ d₀ q b L T R : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hTmax : T ≤ 1)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (i : JetLattice.Label) {t : ℝ} (ht : t ∈ Ioc 0 T) (p : JetPrototype.Phase) :
    physical q (rebuilt s₀ η K α γ d₀ q b L T N F i) (t,p) ≤
      JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
        (shift (displacement i.lattice) p) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
