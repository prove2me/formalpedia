-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_HotLimitExtraction_exists_positive_seed_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.exists_positive_seed_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:17:48.101047+00:00
-- url     : https://prove2.me/theorems/cccfe1a2-fe84-4ae3-80d9-c8d979ad9901
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.exists_positive_seed_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.exists_positive_seed` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapEscapingSeed.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapEscapingSeed.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, with `open MeasureTheory Set`, `open scoped ENNReal`, `open BoltzmannNonuniqueness.EuclideanFlight`):
--
--   ```lean
--   theorem HotLimitExtraction.exists_positive_seed_q80 (E : HotLimitExtraction S)
--       (hcarleman : Published.GPV2009CarlemanInput)
--       (hMityagin : Published.Mityagin2020FiveGainParameters)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq₁ : 1 < q) (hq₂ : q < 2)
--       {G : Set ℝ} (hG : ∀ᵐ t ∂volume, t ∈ G) :
--       ∃ t ∈ Ioc (0:ℝ) 1, t ∈ G ∧ ∃ n : ℕ,
--         0 < WeakTime.phaseSlice (E.hotLimit ∘ hotCharacteristicEquiv) t (seedPortion n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.EuclideanFlight.CharacteristicPhase`, `OAI.BoltzmannNonuniqueness.EuclideanFlight.hotCharacteristicEquiv`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.ShrinkingCapFamily`, `OAI.BoltzmannNonuniqueness.JetPrototype.Space`, `OAI.BoltzmannNonuniqueness.VelocityWeight.Transverse`, `OAI.BoltzmannNonuniqueness.WeakTime.Phase`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotKineticPhase`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotLimit` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.seedPortion`, `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput`, `OAI.BoltzmannNonuniqueness.Published.Mityagin2020FiveGainParameters` and `OAI.BoltzmannNonuniqueness.WeakTime.phaseSlice` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_construction_parameters_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapEscapingSeed.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.exists_positive_seed)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.exists_positive_seed_q80 (E : HotLimitExtraction S)
    (hcarleman : Published.GPV2009CarlemanInput)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {G : Set ℝ} (hG : ∀ᵐ t ∂volume, t ∈ G) :
    ∃ t ∈ Ioc (0:ℝ) 1, t ∈ G ∧ ∃ n : ℕ,
      0 < WeakTime.phaseSlice (E.hotLimit ∘ hotCharacteristicEquiv) t (seedPortion n) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end
