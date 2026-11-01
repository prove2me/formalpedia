-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_eventually_mixedPrelimitMeasure_gaussian_bound_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_mixedPrelimitMeasure_gaussian_bound_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:12:55.251992+00:00
-- url     : https://prove2.me/theorems/c3c13e2c-b2a3-48c1-b30c-2551b33ad9f9
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_mixedPrelimitMeasure_gaussian_bound_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_mixedPrelimitMeasure_gaussian_bound` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapMixedCollisionLimits.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapMixedCollisionLimits.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology`, `open BoltzmannNonuniqueness.VelocityMoment`):
--
--   ```lean
--   theorem eventually_mixedPrelimitMeasure_gaussian_bound_q80 (S : AttainedCapSequence F)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
--       (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
--       {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U) :
--       ∀ᶠ n in atTop,
--         (∫⁻ z, ENNReal.ofReal (weight z.2.1*weight z.2.2)
--           ∂S.mixedPrelimitMeasure (κ n) (coldCylinderVolume a A R)) ≤
--         ENNReal.ofReal ((escapedConstant s₀ η K α d₀*hotConstant q+
--           JetEnvelopeGain.momentConstant K α γ/a)*((A+1)*hotConstant q))*
--           coldCylinderVolume a A R univ
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.ShrinkingCapFamily`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.escapedConstant`, `OAI.BoltzmannNonuniqueness.JetEnvelopeGain.momentConstant`, `OAI.BoltzmannNonuniqueness.JetPrototype.Space`, `OAI.BoltzmannNonuniqueness.VelocityMoment.hotConstant`, `OAI.BoltzmannNonuniqueness.VelocityMoment.weight`, `OAI.BoltzmannNonuniqueness.VelocityWeight.Transverse`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairPhase`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.mixedPrelimitMeasure` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.normalizedHorizon` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.characteristic_test_balance_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.gain_measure_separated_limit_q80` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.loss_measure_compact_limit_q80` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapMixedCollisionLimits.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_mixedPrelimitMeasure_gaussian_bound)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A000

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem eventually_mixedPrelimitMeasure_gaussian_bound_q80 (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U) :
    ∀ᶠ n in atTop,
      (∫⁻ z, ENNReal.ofReal (weight z.2.1*weight z.2.2)
        ∂S.mixedPrelimitMeasure (κ n) (coldCylinderVolume a A R)) ≤
      ENNReal.ofReal ((escapedConstant s₀ η K α d₀*hotConstant q+
        JetEnvelopeGain.momentConstant K α γ/a)*((A+1)*hotConstant q))*
        coldCylinderVolume a A R univ := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end
