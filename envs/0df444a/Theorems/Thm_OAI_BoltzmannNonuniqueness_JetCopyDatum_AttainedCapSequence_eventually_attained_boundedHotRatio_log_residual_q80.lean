-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_eventually_attained_boundedHotRatio_log_residual_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_attained_boundedHotRatio_log_residual_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:21:32.592682+00:00
-- url     : https://prove2.me/theorems/2d6fcece-5552-4416-9e2e-962e2cb60feb
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_attained_boundedHotRatio_log_residual_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_attained_boundedHotRatio_log_residual` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapCoefficientExtraction.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapCoefficientExtraction.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, with `open MeasureTheory Filter Set`, `open scoped ENNReal Topology`, `open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.PositiveIteration`, `open BoltzmannNonuniqueness.VelocityWeight`):
--
--   ```lean
--   theorem eventually_attained_boundedHotRatio_log_residual_q80
--       (hcarleman : Published.GPV2009CarlemanInput) (S : AttainedCapSequence F)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ)
--       {a : ℝ} (ha : 0 < a) :
--       let B := (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
--         JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (2 : ℕ))
--       ∀ᶠ n in atTop, ∀ k : ℕ, ∀ t ∈ Icc a (S.time (κ n)/S.radius (κ n)),
--         ∀ᵐ p : Velocity × Velocity,
--         ENNReal.ofReal (S.boundedHotRatio (κ n) ((t,p.1),p.2)) ≤
--           ((ENNReal.ofReal (a+S.coldFraction (κ n))+S.positiveSourceError B 1 (κ n))*
--             ENNReal.ofReal (∑ j ∈ Finset.range k,
--               ((2*JetCoreSheet.growthConstant K α γ q)*Real.log (1/a))^j))+
--           iterate a (positiveMainKernel (S.radius (κ n)) s₀ η K α γ d₀ q (F.indices (κ n)))
--             (fun w => ENNReal.ofReal (S.boundedHotRatio (κ n) w)) k ((t,p.1),p.2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.HotApplication.realBound`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.ShrinkingCapFamily`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.positiveMainKernel`, `OAI.BoltzmannNonuniqueness.JetCoreSheet.growthConstant`, `OAI.BoltzmannNonuniqueness.JetEscapedEnvelope.constant`, `OAI.BoltzmannNonuniqueness.JetEscapedEnvelope.exponent`, `OAI.BoltzmannNonuniqueness.JetMainGain.coefficient`, `OAI.BoltzmannNonuniqueness.Published.KineticPhase`, `OAI.BoltzmannNonuniqueness.Published.SpaceTime`, `OAI.BoltzmannNonuniqueness.Published.Velocity`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.boundedHotRatio`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldFraction`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.positiveSourceError` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.radius` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.PositiveIteration.iterate` and `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.exists_positive_seed_q80` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.full_vanishing_impossible_q80` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapCoefficientExtraction.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_attained_boundedHotRatio_log_residual)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.PositiveIteration
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem eventually_attained_boundedHotRatio_log_residual_q80
    (hcarleman : Published.GPV2009CarlemanInput) (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ)
    {a : ℝ} (ha : 0 < a) :
    let B := (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (2 : ℕ))
    ∀ᶠ n in atTop, ∀ k : ℕ, ∀ t ∈ Icc a (S.time (κ n)/S.radius (κ n)),
      ∀ᵐ p : Velocity × Velocity,
      ENNReal.ofReal (S.boundedHotRatio (κ n) ((t,p.1),p.2)) ≤
        ((ENNReal.ofReal (a+S.coldFraction (κ n))+S.positiveSourceError B 1 (κ n))*
          ENNReal.ofReal (∑ j ∈ Finset.range k,
            ((2*JetCoreSheet.growthConstant K α γ q)*Real.log (1/a))^j))+
        iterate a (positiveMainKernel (S.radius (κ n)) s₀ η K α γ d₀ q (F.indices (κ n)))
          (fun w => ENNReal.ofReal (S.boundedHotRatio (κ n) w)) k ((t,p.1),p.2) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end
