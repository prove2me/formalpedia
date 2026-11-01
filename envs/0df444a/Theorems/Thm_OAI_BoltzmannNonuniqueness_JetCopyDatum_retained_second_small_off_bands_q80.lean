-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_retained_second_small_off_bands_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.retained_second_small_off_bands_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:14:52.556546+00:00
-- url     : https://prove2.me/theorems/8be10d79-ba19-4377-b7eb-68d45efc7ffe
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.retained_second_small_off_bands_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.retained_second_small_off_bands` of [lean/OAI/MathematicalPhysics/Boltzmann/Branching/RetainedAxialDecay.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/RetainedAxialDecay.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set`, `open scoped ENNReal`, `open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AxialFlow`, `open BoltzmannNonuniqueness.JetLattice`):
--
--   ```lean
--   theorem retained_second_small_off_bands_q80 {K α γ q a δ : ℝ} (hK : 0 ≤ K)
--       (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
--       (ha : 0 < a) (hδ : 0 < δ) :
--       ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ b : ℝ, 0 < b → ∀ ε : ℝ, 0 < ε →
--         ∃ ρ : ℝ, 0 < ρ ∧ ∀ {r s₀ η d₀ M L T t₁ t₂ : ℝ} {N : ℕ},
--         0 < r → 0 < s₀ → s₀ ≤ 1/8 → 0 < η → η ≤ Real.log 2 →
--         0 < d₀ → d₀ ≤ 1 → d₀*(r*M)^10 ≤ min δ b/4 → r*T*L < 1/4 →
--         a ≤ t₂ → t₂ ≤ t₁ → t₁ ≤ T →
--         ∀ (i : Label) (x w : Velocity) (S : Finset ℝ),
--         (t₁,x) ∈ mainCoreRegion s₀ η r N i → ‖w‖ ≤ L → ‖transverse w‖ ≤ ρ →
--         (∀ j < N, μ₀ ≤ JetGeometry.jetScale s₀ η j/r →
--           JetGeometry.jetScale s₀ η j/r ≤ M → JetGeometry.jetScale s₀ η j/r ∈ S) →
--         axial w ∉ bands (collapsedCenters α t₁ (axial (x-r⁻¹ • latticeVector i.lattice))) δ →
--         axial w ∉ bands (profileCenters α γ t₁ (axial (x-r⁻¹ • latticeVector i.lattice)) S) b →
--         retainedFreeKernel r s₀ η K α γ d₀ q M N ((t₂,x-(t₁-t₂) • w),w) univ ≤
--           ENNReal.ofReal ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.AxialFlow.bands`, `OAI.BoltzmannNonuniqueness.AxialFlow.collapsedCenters`, `OAI.BoltzmannNonuniqueness.AxialFlow.profileCenters`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.latticeVector`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreRegion`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.retainedFreeKernel`, `OAI.BoltzmannNonuniqueness.JetGeometry.jetScale`, `OAI.BoltzmannNonuniqueness.JetLattice.Label`, `OAI.BoltzmannNonuniqueness.Published.KineticPhase`, `OAI.BoltzmannNonuniqueness.Published.SpaceTime`, `OAI.BoltzmannNonuniqueness.Published.Velocity`, `OAI.BoltzmannNonuniqueness.VelocityWeight.Transverse`, `OAI.BoltzmannNonuniqueness.VelocityWeight.axial` and `OAI.BoltzmannNonuniqueness.VelocityWeight.transverse` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_pair_uniform_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/RetainedAxialDecay.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.retained_second_small_off_bands)

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

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem retained_second_small_off_bands_q80 {K α γ q a δ : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hδ : 0 < δ) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ b : ℝ, 0 < b → ∀ ε : ℝ, 0 < ε →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ {r s₀ η d₀ M L T t₁ t₂ : ℝ} {N : ℕ},
      0 < r → 0 < s₀ → s₀ ≤ 1/8 → 0 < η → η ≤ Real.log 2 →
      0 < d₀ → d₀ ≤ 1 → d₀*(r*M)^10 ≤ min δ b/4 → r*T*L < 1/4 →
      a ≤ t₂ → t₂ ≤ t₁ → t₁ ≤ T →
      ∀ (i : Label) (x w : Velocity) (S : Finset ℝ),
      (t₁,x) ∈ mainCoreRegion s₀ η r N i → ‖w‖ ≤ L → ‖transverse w‖ ≤ ρ →
      (∀ j < N, μ₀ ≤ JetGeometry.jetScale s₀ η j/r →
        JetGeometry.jetScale s₀ η j/r ≤ M → JetGeometry.jetScale s₀ η j/r ∈ S) →
      axial w ∉ bands (collapsedCenters α t₁ (axial (x-r⁻¹ • latticeVector i.lattice))) δ →
      axial w ∉ bands (profileCenters α γ t₁ (axial (x-r⁻¹ • latticeVector i.lattice)) S) b →
      retainedFreeKernel r s₀ η K α γ d₀ q M N ((t₂,x-(t₁-t₂) • w),w) univ ≤
        ENNReal.ofReal ε := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
