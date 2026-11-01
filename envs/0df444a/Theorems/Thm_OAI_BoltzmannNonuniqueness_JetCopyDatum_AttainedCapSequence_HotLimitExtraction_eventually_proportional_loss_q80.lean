-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_HotLimitExtraction_eventually_proportional_loss_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_proportional_loss_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:18:46.261151+00:00
-- url     : https://prove2.me/theorems/75161454-5212-49ac-b3f8-b1291e7780fc
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_proportional_loss_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_proportional_loss` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapCoveredDamping.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapCoveredDamping.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, with `open MeasureTheory Filter Set`, `open scoped Topology ENNReal`, `open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.VelocityMoment`):
--
--   ```lean
--   theorem HotLimitExtraction.eventually_proportional_loss_q80 (E : HotLimitExtraction S)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq : q < 2) (hl : 0 < E.fraction) {A : ℝ} (hAmax : A ≤ 1)
--       (hA : ENNReal.ofReal A < E.horizon) :
--       ∀ᶠ n in atTop, ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 A →
--         -(2*Real.pi*(‖u.2.2‖+1)*positiveFractionLoss s₀ η K α γ d₀ q E.fraction)*
--           S.normalizedHot (E.indices n) u ≤ S.rescaledHotSource (E.indices n) u
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.ShrinkingCapFamily`, `OAI.BoltzmannNonuniqueness.JetPrototype.Phase`, `OAI.BoltzmannNonuniqueness.JetPrototype.Space`, `OAI.BoltzmannNonuniqueness.VelocityWeight.Transverse`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.normalizedHot`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.positiveFractionLoss` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.rescaledHotSource` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.WeightedLocal.spacetimeVolume` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.exists_positive_seed_q80` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.full_vanishing_impossible_q80` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapCoveredDamping.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_proportional_loss)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.eventually_proportional_loss_q80 (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hl : 0 < E.fraction) {A : ℝ} (hAmax : A ≤ 1)
    (hA : ENNReal.ofReal A < E.horizon) :
    ∀ᶠ n in atTop, ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 A →
      -(2*Real.pi*(‖u.2.2‖+1)*positiveFractionLoss s₀ η K α γ d₀ q E.fraction)*
        S.normalizedHot (E.indices n) u ≤ S.rescaledHotSource (E.indices n) u := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end
