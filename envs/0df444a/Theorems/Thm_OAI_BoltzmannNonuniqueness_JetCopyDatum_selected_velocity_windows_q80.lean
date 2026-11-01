-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_selected_velocity_windows_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_velocity_windows_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:15:34.989567+00:00
-- url     : https://prove2.me/theorems/79cd9ba5-7158-42ae-8fdf-a75ec0066c6d
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_velocity_windows_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_velocity_windows` of [lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedOriginDeletion.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedOriginDeletion.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology`, `open BoltzmannNonuniqueness.VelocityWeight`):
--
--   ```lean
--   theorem selected_velocity_windows_q80 {K α γ q a ε R₀ b₀ s₀ η d₀ : ℝ} (hK : 0 ≤ K)
--       (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
--       (ha : 0 < a) (hε : 0 < ε) (hR₀ : 0 < R₀) (hb₀ : 0 < b₀)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) {r : ℕ → ℝ}
--       (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0)) (m : ℕ) :
--       ∃ R b : ℕ → ℝ, R 0 = R₀ ∧ b 0 = b₀ ∧ (∀ i, 0 < R i) ∧ (∀ i, 0 < b i) ∧
--         ∀ᶠ n in atTop, ∀ i < m, ∀ (N : ℕ) (z : Published.KineticPhase),
--           a ≤ z.1.1 → z.2 ∈ velocityWindow (R i) (b i) →
--           selectedFreeKernel (r n) s₀ η K α γ d₀ q N z
--             (velocityWindow (R (i+1)) (b (i+1)))ᶜ ≤
--             ENNReal.ofReal ε+ENNReal.ofReal ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedFreeKernel`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.velocityWindow`, `OAI.BoltzmannNonuniqueness.Published.KineticPhase`, `OAI.BoltzmannNonuniqueness.Published.SpaceTime` and `OAI.BoltzmannNonuniqueness.Published.Velocity` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_five_nonaxial_tendsto_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedOriginDeletion.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_velocity_windows)

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

theorem selected_velocity_windows_q80 {K α γ q a ε R₀ b₀ s₀ η d₀ : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hε : 0 < ε) (hR₀ : 0 < R₀) (hb₀ : 0 < b₀)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0)) (m : ℕ) :
    ∃ R b : ℕ → ℝ, R 0 = R₀ ∧ b 0 = b₀ ∧ (∀ i, 0 < R i) ∧ (∀ i, 0 < b i) ∧
      ∀ᶠ n in atTop, ∀ i < m, ∀ (N : ℕ) (z : Published.KineticPhase),
        a ≤ z.1.1 → z.2 ∈ velocityWindow (R i) (b i) →
        selectedFreeKernel (r n) s₀ η K α γ d₀ q N z
          (velocityWindow (R (i+1)) (b (i+1)))ᶜ ≤
          ENNReal.ofReal ε+ENNReal.ofReal ε := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
