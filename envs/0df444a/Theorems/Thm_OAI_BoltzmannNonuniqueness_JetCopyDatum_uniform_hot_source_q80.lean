-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_uniform_hot_source_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.uniform_hot_source_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:28:41.699843+00:00
-- url     : https://prove2.me/theorems/35c7b217-545e-4c73-aa5c-144a8c895f00
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.uniform_hot_source_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.uniform_hot_source` of [lean/OAI/MathematicalPhysics/Boltzmann/Jets/JetFamilyBounds.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Jets/JetFamilyBounds.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory`, `open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.JetLattice`, `open BoltzmannNonuniqueness.JetGeometry`):
--
--   ```lean
--   theorem uniform_hot_source_q80 (hcarleman : Published.GPV2009CarlemanInput)
--       {s₀ η K α γ d₀ q t R z e : ℝ}
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
--       (hq₁ : 1 < q) (hq₂ : q < 2) (ht : 0 < t) (htmax : t ≤ 1/32)
--       (hz : 0 ≤ z) (he : 0 ≤ e) (he₁ : e ≤ 1)
--       (N : ℕ) (x : Velocity) (y : X)
--       {F : X × Velocity → ℝ} {c : Label → X × Velocity → ℝ}
--       (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
--       (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R) (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R)
--       (hSum : ∀ u : Finset Label, ∀ p, ∑ i ∈ u, c i p ≤ F p)
--       (hzero : ∀ i, ¬i.annulus < N → ∀ w, c i (y,w) = 0)
--       (hhot : ∀ w, F (y,w)-(∑' i, c i (y,w)) ≤ z)
--       (htail : ∀ w, (∑' i, escaped s₀ η t N x (fun j => c j (y,w)) i) ≤ e)
--       (hcU : ∀ i w, VelocityWeight.H q w*c i (y,w) ≤ JetSupersolution.U η K α γ
--         (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) t i.positive
--           (JetSpatialBox.shifted x i.lattice,w)) (b L : ℝ) :
--       ∀ᵐ v : Velocity,
--         HotRepresentative.source q b L F (y,v) -
--           (∑' i, HotRepresentative.coldSource q b L F (c i) (y,v)) -
--           L*(F (y,v)-(∑' i, c i (y,v))) ≤
--         (2*JetMainGain.coefficient K α γ q/(jetScale s₀ η N+t))*z +
--           2*HotApplication.realBound q*z^2 +
--           (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*(e/t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.HotApplication.realBound`, `OAI.BoltzmannNonuniqueness.HotRepresentative.coldSource`, `OAI.BoltzmannNonuniqueness.HotRepresentative.source`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.escaped`, `OAI.BoltzmannNonuniqueness.JetGeometry.jetScale`, `OAI.BoltzmannNonuniqueness.JetLattice.Label`, `OAI.BoltzmannNonuniqueness.JetMainGain.coefficient`, `OAI.BoltzmannNonuniqueness.JetPrototype.Space`, `OAI.BoltzmannNonuniqueness.JetSpatialBox.shifted`, `OAI.BoltzmannNonuniqueness.JetSupersolution.U` and `OAI.BoltzmannNonuniqueness.VelocityWeight.H` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.cold_source_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.hot_net_source_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_dormant_approximation_family_q80` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_zero_solution_large_q80` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Jets/JetFamilyBounds.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.uniform_hot_source)

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

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetCopyDatum

variable {X : Type*} [MeasurableSpace X]

theorem uniform_hot_source_q80 (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q t R z e : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (ht : 0 < t) (htmax : t ≤ 1/32)
    (hz : 0 ≤ z) (he : 0 ≤ e) (he₁ : e ≤ 1)
    (N : ℕ) (x : Velocity) (y : X)
    {F : X × Velocity → ℝ} {c : Label → X × Velocity → ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R) (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R)
    (hSum : ∀ u : Finset Label, ∀ p, ∑ i ∈ u, c i p ≤ F p)
    (hzero : ∀ i, ¬i.annulus < N → ∀ w, c i (y,w) = 0)
    (hhot : ∀ w, F (y,w)-(∑' i, c i (y,w)) ≤ z)
    (htail : ∀ w, (∑' i, escaped s₀ η t N x (fun j => c j (y,w)) i) ≤ e)
    (hcU : ∀ i w, VelocityWeight.H q w*c i (y,w) ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) t i.positive
        (JetSpatialBox.shifted x i.lattice,w)) (b L : ℝ) :
    ∀ᵐ v : Velocity,
      HotRepresentative.source q b L F (y,v) -
        (∑' i, HotRepresentative.coldSource q b L F (c i) (y,v)) -
        L*(F (y,v)-(∑' i, c i (y,v))) ≤
      (2*JetMainGain.coefficient K α γ q/(jetScale s₀ η N+t))*z +
        2*HotApplication.realBound q*z^2 +
        (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*(e/t) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
