-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_HotLimitExtraction_cold_away_axis_weak_limit_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.cold_away_axis_weak_limit_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:08:42.170993+00:00
-- url     : https://prove2.me/theorems/dbf005dc-cd00-460e-b95e-ffddffda6e31
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.cold_away_axis_weak_limit_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.cold_away_axis_weak_limit` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapColdAverages.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapColdAverages.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology`):
--
--   ```lean
--   theorem HotLimitExtraction.cold_away_axis_weak_limit_q80 (E : HotLimitExtraction S)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq : q < 2) {a A δ R : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon)
--       (hδ : 0 < δ) (hR : 0 ≤ R)
--       (Ω₁ : Set VelocityWeight.Transverse) (hΩ₁ : IsCompact Ω₁)
--       (hlo : ∀ y ∈ Ω₁, δ ≤ ‖y‖) (hhi : ∀ y ∈ Ω₁, ‖y‖ ≤ R)
--       (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂) (hax : ∀ z ∈ Ω₂, |z| ≤ R)
--       {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
--       Published.WeakL1Converges
--         ((volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)))
--         (fun n => S.coldAverage (E.indices n) ψ)
--         (fun z => ∫ v, ψ v ∂E.background (max 0 z.1) z.2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.ShrinkingCapFamily`, `OAI.BoltzmannNonuniqueness.JetPrototype.Space`, `OAI.BoltzmannNonuniqueness.JetPrototype.spaceVolume`, `OAI.BoltzmannNonuniqueness.Published.WeakL1Converges`, `OAI.BoltzmannNonuniqueness.VelocityWeight.Transverse`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldAverage` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.background` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.cold_spacetime_weakStar_limit_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapColdAverages.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.cold_away_axis_weak_limit)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A000

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

namespace JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.cold_away_axis_weak_limit_q80 (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {a A δ R : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon)
    (hδ : 0 < δ) (hR : 0 ≤ R)
    (Ω₁ : Set VelocityWeight.Transverse) (hΩ₁ : IsCompact Ω₁)
    (hlo : ∀ y ∈ Ω₁, δ ≤ ‖y‖) (hhi : ∀ y ∈ Ω₁, ‖y‖ ≤ R)
    (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂) (hax : ∀ z ∈ Ω₂, |z| ≤ R)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges
      ((volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)))
      (fun n => S.coldAverage (E.indices n) ψ)
      (fun z => ∫ v, ψ v ∂E.background (max 0 z.1) z.2) := by
  sorry

end JetCopyDatum.AttainedCapSequence
end BoltzmannNonuniqueness

end

end

end OAI
end
