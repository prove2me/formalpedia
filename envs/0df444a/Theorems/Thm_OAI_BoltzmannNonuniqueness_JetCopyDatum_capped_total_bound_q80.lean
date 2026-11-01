-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_capped_total_bound_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_total_bound_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:14:29.157284+00:00
-- url     : https://prove2.me/theorems/e138d83f-7f19-4eed-bd18-7345569f4eab
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_total_bound_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_total_bound` of [lean/OAI/MathematicalPhysics/Boltzmann/Jets/JetContinuation.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Jets/JetContinuation.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set`, `open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation`, `open BoltzmannNonuniqueness.WeightedLocalControl`):
--
--   ```lean
--   theorem capped_total_bound_q80 {s₀ η K α γ d₀ q b L T R δ : ℝ}
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
--       (hR : 0 ≤ R) (hTmax : T ≤ 1/32) (hδ : 0 < δ)
--       (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
--       (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀m : Measurable h₀) (hh₀ : ∀ p, 0 ≤ h₀ p)
--       (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
--       (F : PeriodicMildState q b L T R (initial s₀ η K α γ d₀ q N h₀))
--       (hcap : F.hotPeak δ (color s₀ η K α γ d₀ q N) ≤ 1) :
--       ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (t,p) ≤
--         WeightedFiniteSeed.amplitude s₀ η K d₀ N+coldNormBound s₀ η K α d₀ N+T+δ
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.CutoffLipschitz.frequencyConstant`, `OAI.BoltzmannNonuniqueness.FlightMeasure.phaseVolume`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.coldNormBound`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.color`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.initial`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.instCountableLabel`, `OAI.BoltzmannNonuniqueness.JetLattice.Label`, `OAI.BoltzmannNonuniqueness.JetPrototype.Phase`, `OAI.BoltzmannNonuniqueness.JetPrototype.Space`, `OAI.BoltzmannNonuniqueness.VelocityWeight.Transverse`, `OAI.BoltzmannNonuniqueness.WeightedFiniteSeed.amplitude`, `OAI.BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState` and `OAI.BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState.hotPeak` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_cap_solution_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Jets/JetContinuation.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_total_bound)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A000

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem capped_total_bound_q80 {s₀ η K α γ d₀ q b L T R δ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1/32) (hδ : 0 < δ)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀m : Measurable h₀) (hh₀ : ∀ p, 0 ≤ h₀ p)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (F : PeriodicMildState q b L T R (initial s₀ η K α γ d₀ q N h₀))
    (hcap : F.hotPeak δ (color s₀ η K α γ d₀ q N) ≤ 1) :
    ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (t,p) ≤
      WeightedFiniteSeed.amplitude s₀ η K d₀ N+coldNormBound s₀ η K α d₀ N+T+δ := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
