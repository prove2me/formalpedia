-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_GeometricBackground_geometric_common_block_growth_q80
-- name    : OAI.BoltzmannNonuniqueness.GeometricBackground.geometric_common_block_growth_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:18:37.2124+00:00
-- url     : https://prove2.me/theorems/aaaee07d-82a0-4114-88a8-67b6ca2459f2
-- title:
--   OAI.BoltzmannNonuniqueness.GeometricBackground.geometric_common_block_growth_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.GeometricBackground.geometric_common_block_growth` of [lean/OAI/MathematicalPhysics/Boltzmann/Jets/GeometricCommonBlock.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Jets/GeometricCommonBlock.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.GeometricBackground`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal NNReal ProbabilityTheory`, `open BoltzmannNonuniqueness.ReferenceGeometry BoltzmannNonuniqueness.VelocityWeight`):
--
--   ```lean
--   theorem geometric_common_block_growth_q80 {d κ : ℝ}
--       (hd : 0 < d) (hdsmall : d ≤ 1/32) (hκ : 0 < κ) (hκsmall : κ < 1)
--       (hg : (referenceClock:ℝ)*κ < referenceGrowth) :
--       ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ N : ℕ, ∃ ε γ₀ : ℝ,
--         0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
--         ∀ {θ η α γ K b W s Δ a l : ℝ}, (hθ : 0 < θ) →
--         0 < η → η ≤ Real.log (1+ε/20) →
--         (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
--         0 < K → 480*(8*A₀) ≤ ε*K → 0 < b → W ≤ κ*b/200 →
--         s ∈ Icc b (b+W) → (8*κ*A₀/K)*s ≤ Δ → Δ ≤ (16*κ*A₀/K)*s → Δ ≤ W →
--         a ≤ s → 0 ≤ l →
--         ∀ (x : V) (v : RetainedState), (x,(v:V)) ∈ lateBox κ d s →
--         Real.exp η*l+6*Δ < ‖transverse x‖ →
--         (6:ℝ≥0∞) < localizedHistoryBlockMass
--           (beamCoefficients hθ hα hγ η (κ*b)) (K/(4*(κ*b)))
--           (48*Real.pi*K/(κ*b)) (s+Δ) a η l s
--           (characteristicHistoryCore_measurable b (κ*b/4) ((κ*b) • firstAxis))
--           (lateBox κ d (s+Δ)) N
--           (flightCharacteristicEquiv (s+Δ) (Δ,(x,(v:V))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.GeometricBackground.beamCoefficients`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.PhysicalFlightState`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.V`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.firstAxis`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.lateBox`, `OAI.BoltzmannNonuniqueness.VelocityWeight.Transverse`, `OAI.BoltzmannNonuniqueness.VelocityWeight.transverse` and `OAI.BoltzmannNonuniqueness.WeakTime.Phase` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.ReferenceGeometry.referenceClock` and `OAI.BoltzmannNonuniqueness.ReferenceGeometry.referenceGrowth` (definitions bundle `OAIQ080A001` of this split); `OAI.BoltzmannNonuniqueness.ReferenceGeometry.RetainedState`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.characteristicHistoryCore`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.characteristicHistoryCore_measurable`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightCharacteristicEquiv`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedHistoryBlockMass` and `OAI.BoltzmannNonuniqueness.ReferenceGeometry.referenceRegion` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.uniform_late_zero_parameters_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Jets/GeometricCommonBlock.lean (declaration OAI.BoltzmannNonuniqueness.GeometricBackground.geometric_common_block_growth)

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

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem geometric_common_block_growth_q80 {d κ : ℝ}
    (hd : 0 < d) (hdsmall : d ≤ 1/32) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock:ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ N : ℕ, ∃ ε γ₀ : ℝ,
      0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ {θ η α γ K b W s Δ a l : ℝ}, (hθ : 0 < θ) →
      0 < η → η ≤ Real.log (1+ε/20) →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 < K → 480*(8*A₀) ≤ ε*K → 0 < b → W ≤ κ*b/200 →
      s ∈ Icc b (b+W) → (8*κ*A₀/K)*s ≤ Δ → Δ ≤ (16*κ*A₀/K)*s → Δ ≤ W →
      a ≤ s → 0 ≤ l →
      ∀ (x : V) (v : RetainedState), (x,(v:V)) ∈ lateBox κ d s →
      Real.exp η*l+6*Δ < ‖transverse x‖ →
      (6:ℝ≥0∞) < localizedHistoryBlockMass
        (beamCoefficients hθ hα hγ η (κ*b)) (K/(4*(κ*b)))
        (48*Real.pi*K/(κ*b)) (s+Δ) a η l s
        (characteristicHistoryCore_measurable b (κ*b/4) ((κ*b) • firstAxis))
        (lateBox κ d (s+Δ)) N
        (flightCharacteristicEquiv (s+Δ) (Δ,(x,(v:V)))) := by
  sorry

end BoltzmannNonuniqueness.GeometricBackground

end

end OAI
end
