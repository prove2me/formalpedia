-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_PlaneLocalWeakComplex_jacobian_area_limit
-- name    : OAI.CircleDomainRigidity.PlaneLocalWeakComplex.jacobian_area_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T05:12:59.278018+00:00
-- url     : https://prove2.me/theorems/399e6885-f7c0-4aa7-ac07-b77fbc01809e
-- title:
--   OAI.CircleDomainRigidity.PlaneLocalWeakComplex.jacobian_area_limit: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.PlaneLocalWeakComplex.jacobian_area_limit` of [lean/OAI/Analysis/CircleDomains/Rigidity/ConductivityJacobianLimit.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Rigidity/ConductivityJacobianLimit.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity`, with `open Set Filter Function MeasureTheory Metric`, `open scoped Topology`):
--
--   ```lean
--    theorem PlaneLocalWeakComplex.jacobian_area_limit
--       {φ : ℂ → ℂ} (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
--       (hgreen : UnorientedFiniteCircleGreenFormula) (hφ : Continuous φ)
--       {F : Set EuclideanPlane} (hF : IsCompact F)
--       (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ)
--       {r₀ : ℝ} (hr₀ : 0 < r₀) (hFr : F ⊆ ball 0 r₀)
--       {c : ℂ} {T : ℂ → ℂ} (hT : AnalyticAt ℂ T 0)
--       (hexp : ∀ z : ℂ, z ≠ 0 → φ z-z = c*z⁻¹+z⁻¹^2*T z⁻¹) :
--       Tendsto (fun R : ℝ =>
--         (∫ x in ball (0 : EuclideanPlane) R,
--           D.realGradient x 0 * D.imagGradient x 1 -
--             D.realGradient x 1 * D.imagGradient x 0) -
--           (volume (ball (0 : EuclideanPlane) R)).toReal) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.EuclideanPlane`, `OAI.CircleDomainRigidity.PlaneLocalWeakComplex` and `OAI.CircleDomainRigidity.complexPlaneCoordinates` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.UnorientedFiniteCircleGreenFormula` (definitions bundle `Q146C005` of this split).
--
--   **Used by.** The proof of `OAI.CircleDomainRigidity.exists_principal_conductivity_energy_scalar` of this split imports it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Rigidity/ConductivityJacobianLimit.lean (declaration OAI.CircleDomainRigidity.PlaneLocalWeakComplex.jacobian_area_limit)

import Mathlib
import Definitions.Def_Q146C005

section

attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem PlaneLocalWeakComplex.jacobian_area_limit
    {φ : ℂ → ℂ} (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hgreen : UnorientedFiniteCircleGreenFormula) (hφ : Continuous φ)
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hFr : F ⊆ ball 0 r₀)
    {c : ℂ} {T : ℂ → ℂ} (hT : AnalyticAt ℂ T 0)
    (hexp : ∀ z : ℂ, z ≠ 0 → φ z-z = c*z⁻¹+z⁻¹^2*T z⁻¹) :
    Tendsto (fun R : ℝ =>
      (∫ x in ball (0 : EuclideanPlane) R,
        D.realGradient x 0 * D.imagGradient x 1 -
          D.realGradient x 1 * D.imagGradient x 0) -
        (volume (ball (0 : EuclideanPlane) R)).toReal) atTop (𝓝 0) := by
  sorry

end CircleDomainRigidity

end

end OAI
end
