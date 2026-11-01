-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_selected_pair_uniform_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_pair_uniform_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:15:00.529532+00:00
-- url     : https://prove2.me/theorems/26efe4cf-01b3-480b-983a-14e5c751077f
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_pair_uniform_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_pair_uniform` of [lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedTwoGainLimit.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedTwoGainLimit.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology`, `open BoltzmannNonuniqueness.VelocityWeight`):
--
--   ```lean
--   theorem selected_pair_uniform_q80 {ε : ℝ≥0∞} (hε : 0 < ε) :
--       ∀ᶠ n in atTop, ∀ (N : ℕ) (t₁ t₂ : ℝ) (x v : Velocity),
--         a ≤ t₂ → t₂ ≤ t₁ → t₁ ≤ T → ‖v‖ ≤ V → ‖transverse v‖ ≤ b n →
--         selectedPairMass (r n) s₀ η K α γ d₀ q N t₁ t₂ x v ≤ ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedPairMass`, `OAI.BoltzmannNonuniqueness.VelocityWeight.Transverse` and `OAI.BoltzmannNonuniqueness.VelocityWeight.transverse` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.exists_positive_seed_q80` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.full_vanishing_impossible_q80` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedTwoGainLimit.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_pair_uniform)

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
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

attribute [local irreducible] selectedFreeKernel retainedFreeKernel

variable {K α γ q a s₀ η d₀ V T : ℝ}
  (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
  (ha : 0 < a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
  (hηmax : η ≤ Real.log 2) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hV : 0 ≤ V)
  (r b : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
  (hblim : Tendsto b atTop (𝓝 0))

include hK hα hγ hq₁ hq₂ ha hs₀ hsmax hη hηmax hd₀ hdmax hV hr hrlim hblim in
theorem selected_pair_uniform_q80 {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (t₁ t₂ : ℝ) (x v : Velocity),
      a ≤ t₂ → t₂ ≤ t₁ → t₁ ≤ T → ‖v‖ ≤ V → ‖transverse v‖ ≤ b n →
      selectedPairMass (r n) s₀ η K α γ d₀ q N t₁ t₂ x v ≤ ε := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
