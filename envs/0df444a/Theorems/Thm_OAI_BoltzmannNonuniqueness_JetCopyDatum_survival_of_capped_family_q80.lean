-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_survival_of_capped_family_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.survival_of_capped_family_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:28:33.150632+00:00
-- url     : https://prove2.me/theorems/ce029f9e-5f90-4d30-9410-98231f5a89d1
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.survival_of_capped_family_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.survival_of_capped_family` of [lean/OAI/MathematicalPhysics/Boltzmann/Jets/JetContinuation.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Jets/JetContinuation.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set`, `open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry`, `open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocal`, `open BoltzmannNonuniqueness.WeightedTranslation`):
--
--   ```lean
--   theorem survival_of_capped_family_q80 {s₀ η K α γ d₀ q b L T R δ : ℝ}
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hTmax : T ≤ 1/32)
--       (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
--       (m N : ℕ) (i : Label) (hi0 : i.lattice = 0)
--       (hwidth : T*(d₀*jetScale s₀ η i.annulus^10) ≤ enlargementWidth η (jetScale s₀ η i.annulus))
--       (hdmax : d₀*jetScale s₀ η i.annulus^10 ≤ 1/64)
--       {F : ℝ × JetPrototype.Phase → ℝ} {c : Label → ℝ × JetPrototype.Phase → ℝ}
--       (hFm : Measurable F) (hcm : ∀ j, Measurable (c j))
--       (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc : ∀ j z, 0 ≤ c j z ∧ c j z ≤ R)
--       (hmild : ColdMildAE q b L T F (color s₀ η K α γ d₀ q N i) (c i))
--       (hsum : ∀ z, Summable (fun j => c j z))
--       (hzero : ∀ j, ¬j.annulus < N → c j = 0)
--       (hU : ∀ r ∈ Ioc 0 T, ∀ j p, H q p.2*c j (r,p) ≤ JetSupersolution.U η K α γ
--         (jetScale s₀ η j.annulus) (d₀*jetScale s₀ η j.annulus^10) r j.positive
--           (shift (displacement j.lattice) p))
--       (hcap : ∀ r ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume,
--         F (r,p)-(∑' j, c j (r,p)) ≤ r+δ)
--       {t : ℝ} (ht : t ∈ Icc 0 T) :
--       ∀ᵐ p ∂FlightMeasure.phaseVolume,
--         Real.exp (-coldOpticalDepth
--           (4*JetBarrierCollision.frequencyConstant*K*d₀*jetScale s₀ η i.annulus^9)
--           (weightFrequencyConstant q 2) δ (escapedFrequencyConstant s₀ η α K d₀ q m) m t)*
--           color s₀ η K α γ d₀ q N i p ≤ c i (t,JetBarrier.flight t p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.weightFrequencyConstant`, `OAI.BoltzmannNonuniqueness.CutoffLipschitz.frequencyConstant`, `OAI.BoltzmannNonuniqueness.FlightMeasure.phaseVolume`, `OAI.BoltzmannNonuniqueness.JetBarrier.flight`, `OAI.BoltzmannNonuniqueness.JetBarrierCollision.frequencyConstant`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.color`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.displacement`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.escapedFrequencyConstant`, `OAI.BoltzmannNonuniqueness.JetGeometry.enlargementWidth`, `OAI.BoltzmannNonuniqueness.JetGeometry.jetScale`, `OAI.BoltzmannNonuniqueness.JetLattice.Label`, `OAI.BoltzmannNonuniqueness.JetLattice.Lattice`, `OAI.BoltzmannNonuniqueness.JetPrototype.Phase`, `OAI.BoltzmannNonuniqueness.JetPrototype.Space`, `OAI.BoltzmannNonuniqueness.JetSupersolution.U`, `OAI.BoltzmannNonuniqueness.VelocityWeight.H`, `OAI.BoltzmannNonuniqueness.VelocityWeight.Transverse` and `OAI.BoltzmannNonuniqueness.WeightedTranslation.shift` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.coldOpticalDepth` (definitions bundle `OAIQ080A001` of this split); `OAI.BoltzmannNonuniqueness.WeightedLocal.ColdMildAE` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.coldLabel_average_free_L1_limit_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Jets/JetContinuation.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.survival_of_capped_family)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem survival_of_capped_family_q80 {s₀ η K α γ d₀ q b L T R δ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hTmax : T ≤ 1/32)
    (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (m N : ℕ) (i : Label) (hi0 : i.lattice = 0)
    (hwidth : T*(d₀*jetScale s₀ η i.annulus^10) ≤ enlargementWidth η (jetScale s₀ η i.annulus))
    (hdmax : d₀*jetScale s₀ η i.annulus^10 ≤ 1/64)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : Label → ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : ∀ j, Measurable (c j))
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc : ∀ j z, 0 ≤ c j z ∧ c j z ≤ R)
    (hmild : ColdMildAE q b L T F (color s₀ η K α γ d₀ q N i) (c i))
    (hsum : ∀ z, Summable (fun j => c j z))
    (hzero : ∀ j, ¬j.annulus < N → c j = 0)
    (hU : ∀ r ∈ Ioc 0 T, ∀ j p, H q p.2*c j (r,p) ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η j.annulus) (d₀*jetScale s₀ η j.annulus^10) r j.positive
        (shift (displacement j.lattice) p))
    (hcap : ∀ r ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume,
      F (r,p)-(∑' j, c j (r,p)) ≤ r+δ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      Real.exp (-coldOpticalDepth
        (4*JetBarrierCollision.frequencyConstant*K*d₀*jetScale s₀ η i.annulus^9)
        (weightFrequencyConstant q 2) δ (escapedFrequencyConstant s₀ η α K d₀ q m) m t)*
        color s₀ η K α γ d₀ q N i p ≤ c i (t,JetBarrier.flight t p) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
