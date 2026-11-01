-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_positiveMainKernel_bound_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.positiveMainKernel_bound_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:16:50.663025+00:00
-- url     : https://prove2.me/theorems/e6382ef3-89ef-46cf-831a-70cf85f5c489
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.positiveMainKernel_bound_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.positiveMainKernel_bound` of [lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedCoreSelection.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedCoreSelection.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory ProbabilityTheory Set`, `open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice`, `open scoped ENNReal`):
--
--   ```lean
--   theorem positiveMainKernel_bound_q80 {r s₀ η K α γ d₀ q : ℝ} (hr : 0 < r)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
--       (hq₁ : 1 < q) (hq₂ : q < 2) (N : ℕ) (z : KineticPhase) (ht : 0 < z.1.1) :
--       positiveMainKernel r s₀ η K α γ d₀ q N z univ ≤
--         ENNReal.ofReal ((2*JetCoreSheet.growthConstant K α γ q)/z.1.1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.JetCopyDatum.positiveMainKernel`, `OAI.BoltzmannNonuniqueness.JetCoreSheet.growthConstant`, `OAI.BoltzmannNonuniqueness.Published.KineticPhase`, `OAI.BoltzmannNonuniqueness.Published.SpaceTime` and `OAI.BoltzmannNonuniqueness.Published.Velocity` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.exists_positive_seed_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.full_vanishing_impossible_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_attained_boundedHotRatio_log_residual_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.positive_five_axial_escape_tendsto_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.positive_five_large_velocity_tendsto_q80` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.positive_five_transverse_escape_tendsto_q80` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedCoreSelection.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.positiveMainKernel_bound)

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

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem positiveMainKernel_bound_q80 {r s₀ η K α γ d₀ q : ℝ} (hr : 0 < r)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (N : ℕ) (z : KineticPhase) (ht : 0 < z.1.1) :
    positiveMainKernel r s₀ η K α γ d₀ q N z univ ≤
      ENNReal.ofReal ((2*JetCoreSheet.growthConstant K α γ q)/z.1.1) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
