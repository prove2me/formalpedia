-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_HotLimitExtraction_full_vanishing_impossible_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.full_vanishing_impossible_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:19:00.626981+00:00
-- url     : https://prove2.me/theorems/e47a8687-b39b-48ec-bbe1-35eebaf0a8df
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.full_vanishing_impossible_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.full_vanishing_impossible` of [lean/OAI/MathematicalPhysics/Boltzmann/Branching/HotFullVanishingContradiction.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/HotFullVanishingContradiction.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, with `open MeasureTheory Set Filter`, `open scoped Topology ENNReal`):
--
--   ```lean
--   theorem HotLimitExtraction.full_vanishing_impossible_q80 (E : HotLimitExtraction S)
--       (hcarleman : Published.GPV2009CarlemanInput)
--       (hMityagin : Published.Mityagin2020FiveGainParameters)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq₁ : 1 < q) (hq₂ : q < 2) (hfinite : E.horizon < ⊤)
--       (hfull : ∀ j, Tendsto (fun n => scaledBoxMass (shrinkingHorizon F.horizonScale n)
--         (EuclideanFlight.density q (F.approximation n).solution.value) j) atTop (𝓝 0)) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.DatumBounds.scale`, `OAI.BoltzmannNonuniqueness.EuclideanFlight.density`, `OAI.BoltzmannNonuniqueness.HotSeedProfile.normalized`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.ShrinkingCapFamily`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.initial`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.scaledBoxMass`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.shrinkingHorizon`, `OAI.BoltzmannNonuniqueness.JetPrototype.Phase`, `OAI.BoltzmannNonuniqueness.WeightedLocalControl.damping`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation` and `OAI.BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput` and `OAI.BoltzmannNonuniqueness.Published.Mityagin2020FiveGainParameters` (definitions bundle `OAIQ080A002` of this split).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_separated_cap_limit_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/HotFullVanishingContradiction.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.full_vanishing_impossible)

import Mathlib
import Definitions.Def_OAIQ080A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.full_vanishing_impossible_q80 (E : HotLimitExtraction S)
    (hcarleman : Published.GPV2009CarlemanInput)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hfinite : E.horizon < ⊤)
    (hfull : ∀ j, Tendsto (fun n => scaledBoxMass (shrinkingHorizon F.horizonScale n)
      (EuclideanFlight.density q (F.approximation n).solution.value) j) atTop (𝓝 0)) : False := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end OAI
end
