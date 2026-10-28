-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryForceSupport_transferred_force_all
-- name    : OAI.ElasticityBoundaryForceSupport.transferred_force_all
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:34:52.832004+00:00
-- url     : https://prove2.me/theorems/9bedadff-0797-4a33-87c6-6cecc568c77e
-- title:
--   OAI.ElasticityBoundaryForceSupport.transferred_force_all: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryForceSupport.transferred_force_all` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryPackets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryPackets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryForceSupport`, with `open Set Filter`, `open scoped Topology BigOperators`, `open ElasticityBoundary ElasticityBoundaryPhysicalTransfer ElasticityBoundaryOperatorLocal`):
--
--   ```lean
--   theorem transferred_force_all (e : OpenPartialHomeomorph X X) {K : Set X}
--       (hK : IsCompact K) (hs : K⊆e.source) {η : X → ℝ} (hηs : tsupport η⊆e.target)
--       (hη : ∀ z∈e '' K, η z=1) (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
--       (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
--       (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
--       (Φ Ψ : X → X) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
--       (hΦ : ∀ y∈K, Φ y=e y) (hΨe : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)
--       {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
--       (x : X) (hx : x∈e.source) (s : I) :
--       (∑ i, frameMatrix Q i s*force l m (transferred e η Q u) i (e x))=
--         strong (chartPrincipal Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m)
--           (chartLower Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m) u s x.ofLp
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityBoundaryChartOperator.X`, `OAI.ElasticityBoundaryChartOperator.Y`, `OAI.ElasticityBoundaryChartOperator.chartPrincipal`, `OAI.ElasticityBoundaryForceSupport.I`, `OAI.ElasticityBoundaryForceSupport.X`, `OAI.ElasticityBoundaryForceSupport.Y`, `OAI.ElasticityBoundaryPhysicalTransfer.transferred`, `OAI.ElasticityBoundaryRotation.I`, `OAI.ElasticityBoundaryRotation.frameMatrix` and `OAI.ElasticityBoundaryStrongLayer.strong` (definitions bundle `OAIQ6El001` of this split); `OAI.ElasticityBoundaryChartOperator.chartLower` and `OAI.ElasticityBoundaryPhysicalTransfer.force` (definitions bundle `OAIQ6El004` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityBoundaryPhysicalMass.transferred_mass_bound` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryPackets.lean (declaration OAI.ElasticityBoundaryForceSupport.transferred_force_all)

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
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryForceSupport
open ElasticityBoundary ElasticityBoundaryPhysicalTransfer ElasticityBoundaryOperatorLocal
  ElasticityBoundaryLocalParametrix ElasticityBoundaryStrongLayer
  ElasticityBoundaryChartOperator ElasticityBoundaryFrameOperator
  ElasticityBoundaryFrameInverse ElasticityBoundaryRotation

theorem transferred_force_all (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : IsCompact K) (hs : K⊆e.source) {η : X → ℝ} (hηs : tsupport η⊆e.target)
    (hη : ∀ z∈e '' K, η z=1) (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (Φ Ψ : X → X) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ y=e y) (hΨe : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)
    {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (x : X) (hx : x∈e.source) (s : I) :
    (∑ i, frameMatrix Q i s*force l m (transferred e η Q u) i (e x))=
      strong (chartPrincipal Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m)
        (chartLower Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m) u s x.ofLp := by
  sorry

end ElasticityBoundaryForceSupport

end
end

end OAI
end
