-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_CompactScalarModel_FlattenedSourceSelection_compact_tests
-- name    : OAI.CircleDomainRigidity.CompactScalarModel.FlattenedSourceSelection.compact_tests
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T05:10:26.491833+00:00
-- url     : https://prove2.me/theorems/01b2f4b6-13b6-45ed-a862-68e9e29f6dd2
-- title:
--   OAI.CircleDomainRigidity.CompactScalarModel.FlattenedSourceSelection.compact_tests: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.CompactScalarModel.FlattenedSourceSelection.compact_tests` of [lean/OAI/Analysis/CircleDomains/Transfer/ModelSelectedTests.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Transfer/ModelSelectedTests.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity.CompactScalarModel`, with `open Set Function Filter MeasureTheory Metric`, `open scoped Topology ContDiff ENNReal`):
--
--   ```lean
--    theorem FlattenedSourceSelection.compact_tests (M : CompactScalarModel G u)
--       (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
--       (hG : IsOpen G) (hconn : IsConnected G)
--       (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
--       (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
--       (hpairs : ∀ i j, i ≠ j → volume ((fun p =>
--         (sphereFromPlaneFunction (u i) p,sphereFromPlaneFunction (u j) p)) '' Gᶜ) = 0)
--       {R d : ℝ} (H : ControlledHeight R d)
--       (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
--         heightLimitGradient H.error₀ H.error₁ x = 0)
--       (W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
--       {A L δ ε : ℝ} (S : FlattenedSourceSelection M H W A L δ ε)
--       (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hsη : HasCompactSupport η)
--       (hηB : ∀ z : ℂ, (z : Sphere) ∉ G → η z = 1) (hsL : tsupport η ⊆ ball 0 L)
--       (θ : EuclideanPlane → ℝ) (hθ : ContDiff ℝ ∞ θ) (hsθ : HasCompactSupport θ)
--       (hθA : tsupport θ ⊆ ball 0 A)
--       (hθF : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), θ x = 1) :
--       let t := appendScalarPair (fun i => flattenValues (S.oldValues i) ∘ u i)
--         (M.compactPrioritySource S.cutoff S.value η)
--         (M.compactHeightSource H (flattenValues S.heightValues) θ)
--       (∀ i, Continuous (t i)) ∧ (∀ i, HasCompactSupport (t i)) ∧
--         Nonempty (∀ i, DeGiorgi.MemW1pWitness 2 (t i) (physicalPlaneDomain G)) ∧
--         (∀ i j, i ≠ j → volume ((fun p =>
--           (sphereFromPlaneFunction (t i) p,sphereFromPlaneFunction (t j) p)) '' Gᶜ) = 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.CompactScalarModel`, `OAI.CircleDomainRigidity.EuclideanPlane`, `OAI.CircleDomainRigidity.PlanarSchoenflies`, `OAI.CircleDomainRigidity.SmoothPlanarSard`, `OAI.CircleDomainRigidity.appendScalarPair`, `OAI.CircleDomainRigidity.extendAtInfinity`, `OAI.CircleDomainRigidity.physicalPlaneDomain`, `OAI.CircleDomainRigidity.sphereFromPlaneFunction` and `OAI.DeGiorgi.MemW1pWitness` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.flattenValues` (definitions bundle `Q146C002` of this split); `OAI.CircleDomainRigidity.ControlledHeight`, `OAI.CircleDomainRigidity.heightLimitGradient`, `OAI.CircleDomainRigidity.CompactScalarModel.FlattenedSourceSelection`, `OAI.CircleDomainRigidity.CompactScalarModel.compactHeightSource` and `OAI.CircleDomainRigidity.CompactScalarModel.compactPrioritySource` (definitions bundle `Q146C004` of this split); `OAI.CircleDomainRigidity.PlanarSobolevCoarea` (definitions bundle `Q146C005` of this split); `OAI.CircleDomainRigidity.Sphere` (the published bundle `Def_KoebeCircleDomains`).
--
--   **Used by.** The proof of `OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRealMask.global_sobolev_of_published_inputs` of this split imports it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Transfer/ModelSelectedTests.lean (declaration OAI.CircleDomainRigidity.CompactScalarModel.FlattenedSourceSelection.compact_tests)

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C004
import Definitions.Def_Q146C005

section

attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem FlattenedSourceSelection.compact_tests (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hpairs : ∀ i j, i ≠ j → volume ((fun p =>
      (sphereFromPlaneFunction (u i) p,sphereFromPlaneFunction (u j) p)) '' Gᶜ) = 0)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    (W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    {A L δ ε : ℝ} (S : FlattenedSourceSelection M H W A L δ ε)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hsη : HasCompactSupport η)
    (hηB : ∀ z : ℂ, (z : Sphere) ∉ G → η z = 1) (hsL : tsupport η ⊆ ball 0 L)
    (θ : EuclideanPlane → ℝ) (hθ : ContDiff ℝ ∞ θ) (hsθ : HasCompactSupport θ)
    (hθA : tsupport θ ⊆ ball 0 A)
    (hθF : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), θ x = 1) :
    let t := appendScalarPair (fun i => flattenValues (S.oldValues i) ∘ u i)
      (M.compactPrioritySource S.cutoff S.value η)
      (M.compactHeightSource H (flattenValues S.heightValues) θ)
    (∀ i, Continuous (t i)) ∧ (∀ i, HasCompactSupport (t i)) ∧
      Nonempty (∀ i, DeGiorgi.MemW1pWitness 2 (t i) (physicalPlaneDomain G)) ∧
      (∀ i j, i ≠ j → volume ((fun p =>
        (sphereFromPlaneFunction (t i) p,sphereFromPlaneFunction (t j) p)) '' Gᶜ) = 0) := by
  sorry

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end
