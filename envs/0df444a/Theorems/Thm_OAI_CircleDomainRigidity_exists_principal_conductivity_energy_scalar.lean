-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_exists_principal_conductivity_energy_scalar
-- name    : OAI.CircleDomainRigidity.exists_principal_conductivity_energy_scalar
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T05:26:05.769387+00:00
-- url     : https://prove2.me/theorems/a96a59fd-d0b0-4f47-adce-52b6932f88e2
-- title:
--   OAI.CircleDomainRigidity.exists_principal_conductivity_energy_scalar: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.exists_principal_conductivity_energy_scalar` of [lean/OAI/Analysis/CircleDomains/Sobolev/PrincipalScalarEnergy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Sobolev/PrincipalScalarEnergy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity`, with `open Set Filter Function MeasureTheory Metric Bornology`, `open scoped Topology`):
--
--   ```lean
--   lemma exists_principal_conductivity_energy_scalar
--       (hsolver : PrincipalConductivityScalarSolver)
--       (hgreen : UnorientedFiniteCircleGreenFormula) {F : Set EuclideanPlane}
--       (hF : IsCompact F) (n : ℕ) (hn : 2 ≤ n) :
--       ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
--         (c : ℂ) (T : ℂ → ℂ),
--         AnalyticAt ℂ T 0 ∧
--         Tendsto (fun z => φ z-z) (cobounded ℂ) (𝓝 0) ∧
--         (∀ z : ℂ, z ≠ 0 → φ z-z = c*z⁻¹+z⁻¹^2*T z⁻¹) ∧
--         (∀ᵐ x ∂volume,
--           D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
--           D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0) ∧
--         DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ ∧
--         Integrable (fun x => (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) ∧
--         (∫ x, (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) +
--           ((n : ℝ)-1)*(∫ x in F, (D.imagGradient x 0)^2+(D.imagGradient x 1)^2) =
--             2*Real.pi*c.re ∧ CompactScalarPullback φ
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.EuclideanPlane`, `OAI.CircleDomainRigidity.PlaneLocalWeakComplex` and `OAI.CircleDomainRigidity.complexPlaneCoordinates` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.CompactScalarPullback` (definitions bundle `Q146C004` of this split); `OAI.CircleDomainRigidity.UnorientedFiniteCircleGreenFormula` and `OAI.CircleDomainRigidity.conductivityValue` (definitions bundle `Q146C005` of this split); `OAI.CircleDomainRigidity.PrincipalConductivityScalarSolver` (definitions bundle `Q146C008` of this split).
--
--   **Used by.** The proof of `OAI.CircleDomainRigidity.exists_small_selected_height_data` of this split imports it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Sobolev/PrincipalScalarEnergy.lean (declaration OAI.CircleDomainRigidity.exists_principal_conductivity_energy_scalar)

import Mathlib
import Definitions.Def_Q146C008

section

attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Function MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_principal_conductivity_energy_scalar
    (hsolver : PrincipalConductivityScalarSolver)
    (hgreen : UnorientedFiniteCircleGreenFormula) {F : Set EuclideanPlane}
    (hF : IsCompact F) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
      (c : ℂ) (T : ℂ → ℂ),
      AnalyticAt ℂ T 0 ∧
      Tendsto (fun z => φ z-z) (cobounded ℂ) (𝓝 0) ∧
      (∀ z : ℂ, z ≠ 0 → φ z-z = c*z⁻¹+z⁻¹^2*T z⁻¹) ∧
      (∀ᵐ x ∂volume,
        D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
        D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0) ∧
      DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ ∧
      Integrable (fun x => (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) ∧
      (∫ x, (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) +
        ((n : ℝ)-1)*(∫ x in F, (D.imagGradient x 0)^2+(D.imagGradient x 1)^2) =
          2*Real.pi*c.re ∧ CompactScalarPullback φ := by
  sorry

end CircleDomainRigidity

end

end OAI
end
