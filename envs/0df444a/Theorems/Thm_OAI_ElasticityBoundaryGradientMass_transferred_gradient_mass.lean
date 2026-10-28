-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryGradientMass_transferred_gradient_mass
-- name    : OAI.ElasticityBoundaryGradientMass.transferred_gradient_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:25:48.68369+00:00
-- url     : https://prove2.me/theorems/40cb2f49-609b-4bea-ab5d-dccd204b2f5e
-- title:
--   OAI.ElasticityBoundaryGradientMass.transferred_gradient_mass: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryGradientMass.transferred_gradient_mass` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryPackets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryPackets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryGradientMass`, with `open Set MeasureTheory Filter`, `open scoped Topology BigOperators`, `open ElasticityBoundaryGradientTransfer ElasticityBoundaryPhysicalTransfer`):
--
--   ```lean
--   lemma transferred_gradient_mass : ∃ C : ℝ, 0≤C ∧ ∀ (u : I → Y → ℂ),
--       (∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) →
--       (∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) →
--       ∀ i d, (∫ x in Ω, ‖dd (transferred e η Q u i) (basis d) x‖^2)≤
--         C*∑ s, ∑ α, (∫ y in H, ‖dpart (u s) α y.ofLp‖^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityBoundaryChainRule.dd` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityBoundaryChartOperator.I`, `OAI.ElasticityBoundaryChartOperator.basis`, `OAI.ElasticityBoundaryGradientMass.I`, `OAI.ElasticityBoundaryGradientMass.X`, `OAI.ElasticityBoundaryGradientMass.Y`, `OAI.ElasticityBoundaryPhysicalTransfer.I`, `OAI.ElasticityBoundaryPhysicalTransfer.X`, `OAI.ElasticityBoundaryPhysicalTransfer.transferred` and `OAI.ElasticityBoundaryStrongLayer.dpart` (definitions bundle `OAIQ6El001` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityBoundaryPacket.Setup.field_gradient_mass` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryPackets.lean (declaration OAI.ElasticityBoundaryGradientMass.transferred_gradient_mass)

import Mathlib
import Definitions.Def_OAIQ6El000
import Definitions.Def_OAIQ6El001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryGradientMass
open ElasticityBoundaryGradientTransfer ElasticityBoundaryPhysicalTransfer
  ElasticityBoundaryChartMass ElasticityBoundaryCompactMatrix ElasticityBoundaryForceSupport
  ElasticityBoundaryFrameOperator ElasticityBoundaryRotation ElasticityBoundaryChainRule
  ElasticityBoundaryStrongLayer ElasticityBoundaryChartOperator

variable (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    {K Ω H : Set X} (hK : IsCompact K) (hs : K⊆e.source)
    (hΩ : MeasurableSet Ω) (hH : MeasurableSet H)
    (hhalf : ∀ y∈e.source, e y∈Ω ↔ y∈H)
    {η : X → ℝ} (hηs : tsupport η⊆e.target) (hη : ∀ z∈e '' K, η z=1)
    (Q : X ≃ₗᵢ[ℝ] X) (Φ Ψ : X → X)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ =ᶠ[𝓝 y] e) (hΨ : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)

include he hK hs hΩ hH hhalf hηs hη hΦs hΨs hΦ hΨ in
lemma transferred_gradient_mass : ∃ C : ℝ, 0≤C ∧ ∀ (u : I → Y → ℂ),
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) →
    (∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) →
    ∀ i d, (∫ x in Ω, ‖dd (transferred e η Q u i) (basis d) x‖^2)≤
      C*∑ s, ∑ α, (∫ y in H, ‖dpart (u s) α y.ofLp‖^2) := by
  sorry

end ElasticityBoundaryGradientMass

end
end

end OAI
end
