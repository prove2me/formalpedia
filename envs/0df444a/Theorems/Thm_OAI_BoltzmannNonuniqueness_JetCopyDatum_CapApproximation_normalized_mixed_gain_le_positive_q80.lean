-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_CapApproximation_normalized_mixed_gain_le_positive_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.normalized_mixed_gain_le_positive_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:24:24.701163+00:00
-- url     : https://prove2.me/theorems/13c4226b-9193-41f8-928f-44c6a974b993
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.normalized_mixed_gain_le_positive_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.normalized_mixed_gain_le_positive` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapMixedPositiveBound.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapMixedPositiveBound.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology`, `open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight`):
--
--   ```lean
--   theorem CapApproximation.normalized_mixed_gain_le_positive_q80 (hcarleman : Published.GPV2009CarlemanInput)
--       {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
--       (F : CapApproximation s₀ η K α γ d₀ q T N)
--       (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
--       (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
--       (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq₁ : 1 < q) (hq₂ : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
--       (x : SpaceTime) (ht : r*x.1 ∈ Ioc 0 T)
--       (b : ℝ) {f : KineticPhase → ℝ} (hf : Measurable f) (hfn : ∀ z, 0 ≤ f z)
--       (hftwo : ∀ z, f z ≤ 2) :
--       ∀ᵐ v : Velocity, ENNReal.ofReal ((2*CollisionCompactness.mixedGainDensity b
--         (F.dilatedCold r) (fun z => H q z.2*f z) (x,v))/H q v) ≤
--           ChartKernel.action (positiveMainKernel r s₀ η K α γ d₀ q N)
--             (fun z => ENNReal.ofReal (f z)) (x,v)+
--             4*(ENNReal.ofReal r*coldGainErrorConstant s₀ η K α d₀ q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.ChartKernel.action`, `OAI.BoltzmannNonuniqueness.CollisionCompactness.mixedGainDensity`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.coldGainErrorConstant`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.positiveMainKernel`, `OAI.BoltzmannNonuniqueness.Published.KineticPhase`, `OAI.BoltzmannNonuniqueness.Published.SpaceTime`, `OAI.BoltzmannNonuniqueness.Published.Velocity`, `OAI.BoltzmannNonuniqueness.VelocityWeight.H` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.dilatedCold` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.positive_coefficient_subsequence_q80` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_attained_boundedHotRatio_log_residual_q80` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapMixedPositiveBound.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.normalized_mixed_gain_le_positive)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.normalized_mixed_gain_le_positive_q80 (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (x : SpaceTime) (ht : r*x.1 ∈ Ioc 0 T)
    (b : ℝ) {f : KineticPhase → ℝ} (hf : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hftwo : ∀ z, f z ≤ 2) :
    ∀ᵐ v : Velocity, ENNReal.ofReal ((2*CollisionCompactness.mixedGainDensity b
      (F.dilatedCold r) (fun z => H q z.2*f z) (x,v))/H q v) ≤
        ChartKernel.action (positiveMainKernel r s₀ η K α γ d₀ q N)
          (fun z => ENNReal.ofReal (f z)) (x,v)+
          4*(ENNReal.ofReal r*coldGainErrorConstant s₀ η K α d₀ q) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
