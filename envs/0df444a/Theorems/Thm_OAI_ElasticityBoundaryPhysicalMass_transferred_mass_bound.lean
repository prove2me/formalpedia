-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryPhysicalMass_transferred_mass_bound
-- name    : OAI.ElasticityBoundaryPhysicalMass.transferred_mass_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:36:01.928538+00:00
-- url     : https://prove2.me/theorems/9b7512f7-62b3-48a8-8703-ed47d65f4f89
-- title:
--   OAI.ElasticityBoundaryPhysicalMass.transferred_mass_bound: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryPhysicalMass.transferred_mass_bound` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryPackets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryPackets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryPhysicalMass`, with `open Set MeasureTheory Filter`, `open scoped Topology BigOperators`, `open ElasticityBoundary ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport`):
--
--   ```lean
--   theorem transferred_mass_bound (e : OpenPartialHomeomorph X X)
--       (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
--       {K Ω H : Set X} (hK : IsCompact K) (hs : K⊆e.source)
--       (hΩ : MeasurableSet Ω) (hH : MeasurableSet H)
--       (hhalf : ∀ y∈e.source, e y∈Ω ↔ y∈H)
--       {η : X → ℝ} (hηs : tsupport η⊆e.target) (hη : ∀ z∈e '' K, η z=1)
--       (Q : X ≃ₗᵢ[ℝ] X) (Φ Ψ : X → X)
--       (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ)
--       (hΦ : ∀ y∈K, Φ =ᶠ[𝓝 y] e) (hΨ : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)
--       {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
--       :
--       ∃ C : ℝ, 0≤C ∧ ∀ (u : I → Y → ℂ),
--         (∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) →
--         (∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) →
--         ∀ i, (∫ x in Ω, ‖force l m (transferred e η Q u) i x‖^2)≤
--           C*∑ s, (∫ y in H, ‖strong (principal Q Φ Ψ l m) (lower Q Φ Ψ l m) u s y.ofLp‖^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityBoundaryPhysicalMass.I`, `OAI.ElasticityBoundaryPhysicalMass.X`, `OAI.ElasticityBoundaryPhysicalMass.Y`, `OAI.ElasticityBoundaryPhysicalMass.principal`, `OAI.ElasticityBoundaryPhysicalTransfer.I`, `OAI.ElasticityBoundaryPhysicalTransfer.transferred` and `OAI.ElasticityBoundaryStrongLayer.strong` (definitions bundle `OAIQ6El001` of this split); `OAI.ElasticityBoundaryPhysicalMass.lower` and `OAI.ElasticityBoundaryPhysicalTransfer.force` (definitions bundle `OAIQ6El004` of this split).
--
--   **Used by.** The proofs of `OAI_ElasticityBoundaryPacket_Setup_field_force_mass` and `OAI.ElasticityBoundaryPacket.Setup.packet` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryPackets.lean (declaration OAI.ElasticityBoundaryPhysicalMass.transferred_mass_bound)

import Mathlib
import Definitions.Def_OAIQ6El004

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryPhysicalMass
open ElasticityBoundary ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryChartMass ElasticityBoundaryChartOperator ElasticityBoundaryRotation
  ElasticityBoundarySmoothOperator ElasticityBoundaryStrongLayer ElasticityBoundaryCutoffLayer
  ElasticityBoundaryFrameOperator

theorem transferred_mass_bound (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    {K Ω H : Set X} (hK : IsCompact K) (hs : K⊆e.source)
    (hΩ : MeasurableSet Ω) (hH : MeasurableSet H)
    (hhalf : ∀ y∈e.source, e y∈Ω ↔ y∈H)
    {η : X → ℝ} (hηs : tsupport η⊆e.target) (hη : ∀ z∈e '' K, η z=1)
    (Q : X ≃ₗᵢ[ℝ] X) (Φ Ψ : X → X)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ =ᶠ[𝓝 y] e) (hΨ : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)
    {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    :
    ∃ C : ℝ, 0≤C ∧ ∀ (u : I → Y → ℂ),
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) →
      (∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) →
      ∀ i, (∫ x in Ω, ‖force l m (transferred e η Q u) i x‖^2)≤
        C*∑ s, (∫ y in H, ‖strong (principal Q Φ Ψ l m) (lower Q Φ Ψ l m) u s y.ofLp‖^2) := by
  sorry

end ElasticityBoundaryPhysicalMass

end
end

end OAI
end
