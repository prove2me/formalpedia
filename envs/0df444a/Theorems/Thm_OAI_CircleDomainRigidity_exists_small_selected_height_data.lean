-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_exists_small_selected_height_data
-- name    : OAI.CircleDomainRigidity.exists_small_selected_height_data
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T05:25:58.098795+00:00
-- url     : https://prove2.me/theorems/c24bd831-48f0-4400-b426-5db361019692
-- title:
--   OAI.CircleDomainRigidity.exists_small_selected_height_data: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.exists_small_selected_height_data` of [lean/OAI/Analysis/CircleDomains/Selection/PreparedHeightSelection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Selection/PreparedHeightSelection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity`, with `open Set Function Filter MeasureTheory Metric`, `open scoped Topology ContDiff ENNReal`):
--
--   ```lean
--    theorem exists_small_selected_height_data
--       {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
--       (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
--       (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
--       (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
--       (hG : IsOpen G) (hconn : IsConnected G) (hinf : OnePoint.infty ∈ G)
--       (hTD : IsTotallyDisconnected Gᶜ)
--       (hB : IsCompact {z : ℂ | (z : Sphere) ∉ G})
--       (hBne : {z : ℂ | (z : Sphere) ∉ G}.Nonempty)
--       (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
--       (Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
--       (hne : Nonempty (CompactScalarModel G u))
--       {R C : ℝ} (hR : 0 < R) (hsource : (((↑) : ℂ → Sphere) '' ball 0 R)ᶜ ⊆ G)
--       (hC : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 C)
--       (A L : ℝ) (θ : EuclideanPlane → ℝ) (hθ : ContDiff ℝ ∞ θ)
--       (hsθ : HasCompactSupport θ) (hθA : tsupport θ ⊆ ball 0 A)
--       {Cθ : ℝ} (hCθ : 0 ≤ Cθ) (hθunit : ∀ x, θ x ∈ Icc (0 : ℝ) 1)
--       (hθd : ∀ x, ‖fderiv ℝ θ x‖ ≤ Cθ)
--       {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
--       ∃ e : ℝ, 0 < e ∧ e < b ∧ ∃ d : ℝ, 0 < d ∧ d < e ∧
--         ∃ M : CompactScalarModel G u, ∃ H : ControlledHeight (3*R+1) d,
--         ∃ S : CompactScalarModel.FlattenedSourceSelection M H Wold A L e e,
--           (∀ z ∈ closedBall 0 A, |H.height z-z.im| < e) ∧
--           (∀ n, support (S.cutoff n) ⊆ ball 0 C) ∧
--           ∃ E : DeGiorgi.MemW1pWitness 2 (planeInverseTransport (extendAtInfinity M.function)
--             (fun y => θ y*(flattenValues S.heightValues (H.height (complexPlaneCoordinates y))-y 1)))
--             (physicalPlaneDomain G),
--             (∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
--               heightLimitGradient H.error₀ H.error₁ x = 0) ∧
--             (∫ x in physicalPlaneDomain G, E.weakGrad x 0^2+E.weakGrad x 1^2) < t^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.CompactScalarModel`, `OAI.CircleDomainRigidity.EuclideanPlane`, `OAI.CircleDomainRigidity.PlanarSchoenflies`, `OAI.CircleDomainRigidity.SmoothPlanarSard`, `OAI.CircleDomainRigidity.complexPlaneCoordinates`, `OAI.CircleDomainRigidity.extendAtInfinity`, `OAI.CircleDomainRigidity.physicalPlaneDomain` and `OAI.DeGiorgi.MemW1pWitness` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.ExteriorCoefficientAreaTheorem` and `OAI.CircleDomainRigidity.flattenValues` (definitions bundle `Q146C002` of this split); `OAI.CircleDomainRigidity.ControlledHeight`, `OAI.CircleDomainRigidity.heightLimitGradient` and `OAI.CircleDomainRigidity.CompactScalarModel.FlattenedSourceSelection` (definitions bundle `Q146C004` of this split); `OAI.CircleDomainRigidity.PlanarSobolevCoarea`, `OAI.CircleDomainRigidity.PrincipalRealBeltrami` and `OAI.CircleDomainRigidity.UnorientedFiniteCircleGreenFormula` (definitions bundle `Q146C005` of this split); `OAI.CircleDomainRigidity.PrincipalConductivityScalarSolver` and `OAI.CircleDomainRigidity.planeInverseTransport` (definitions bundle `Q146C008` of this split); `OAI.CircleDomainRigidity.Sphere` (the published bundle `Def_KoebeCircleDomains`).
--
--   **Used by.** The proof of `OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRealMask.global_sobolev_of_published_inputs` of this split imports it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Selection/PreparedHeightSelection.lean (declaration OAI.CircleDomainRigidity.exists_small_selected_height_data)

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C008

section

attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_small_selected_height_data
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G) (hinf : OnePoint.infty ∈ G)
    (hTD : IsTotallyDisconnected Gᶜ)
    (hB : IsCompact {z : ℂ | (z : Sphere) ∉ G})
    (hBne : {z : ℂ | (z : Sphere) ∉ G}.Nonempty)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    (hne : Nonempty (CompactScalarModel G u))
    {R C : ℝ} (hR : 0 < R) (hsource : (((↑) : ℂ → Sphere) '' ball 0 R)ᶜ ⊆ G)
    (hC : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 C)
    (A L : ℝ) (θ : EuclideanPlane → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hsθ : HasCompactSupport θ) (hθA : tsupport θ ⊆ ball 0 A)
    {Cθ : ℝ} (hCθ : 0 ≤ Cθ) (hθunit : ∀ x, θ x ∈ Icc (0 : ℝ) 1)
    (hθd : ∀ x, ‖fderiv ℝ θ x‖ ≤ Cθ)
    {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    ∃ e : ℝ, 0 < e ∧ e < b ∧ ∃ d : ℝ, 0 < d ∧ d < e ∧
      ∃ M : CompactScalarModel G u, ∃ H : ControlledHeight (3*R+1) d,
      ∃ S : CompactScalarModel.FlattenedSourceSelection M H Wold A L e e,
        (∀ z ∈ closedBall 0 A, |H.height z-z.im| < e) ∧
        (∀ n, support (S.cutoff n) ⊆ ball 0 C) ∧
        ∃ E : DeGiorgi.MemW1pWitness 2 (planeInverseTransport (extendAtInfinity M.function)
          (fun y => θ y*(flattenValues S.heightValues (H.height (complexPlaneCoordinates y))-y 1)))
          (physicalPlaneDomain G),
          (∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
            heightLimitGradient H.error₀ H.error₁ x = 0) ∧
          (∫ x in physicalPlaneDomain G, E.weakGrad x 0^2+E.weakGrad x 1^2) < t^2 := by
  sorry

end CircleDomainRigidity

end

end OAI
end
