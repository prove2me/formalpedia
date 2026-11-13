-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_actual_surface_collar_profile_family
-- name    : OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_surface_collar_profile_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:35:30.127348+00:00
-- url     : https://prove2.me/theorems/51c6ccb9-0ae4-45fd-b67a-7ea7099610a8
-- title:
--   OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_surface_collar_profile_family: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_surface_collar_profile_family` of [lean/OAI/Geometry/SurfaceImmersion/Whitney/ActualSurfaceCollarProfiles.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Whitney/ActualSurfaceCollarProfiles.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.SurfaceVelocityFamily`, with `open Set Filter`, `open scoped ContDiff Topology Matrix`, `open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry SurfaceJetCoordinates GeometryPreservation`):
--
--   ```lean
--   theorem actual_surface_collar_profile_family {F n : Base → Vec} {a : Base → ℝ}
--       (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
--       {T U : Set Base} (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
--       (hn : ContDiffOn ℝ ∞ n U)
--       (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ F p))
--       (hN : ∀ p ∈ U, coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧
--         n p ⬝ᵥ n p = 1)
--       (hHess : ∀ p ∈ U, 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy)
--       (haT : ∀ p ∈ T, 0 ≤ a p)
--       (hboundary : ∀ p ∈ T, a p = 0 → realSecondForm F dy dy p ≠ 0 ∧
--         normalize (realSecondForm F dy dy p) ≠ -n p)
--       :
--       ∃ Ω : TopologicalSpace.Opens GeometricJet, CollarVelocity.jetSection F '' T ⊆ Ω ∧
--         (Ω : Set GeometricJet) ⊆ supportedJetDomain U n a ∧
--         ∃ e₁ e₂ : GeometricJet → Vec,
--           ContDiffOn ℝ ∞ e₁ Ω ∧ ContDiffOn ℝ ∞ e₂ Ω ∧
--           (∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
--             j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0) ∧
--         (∃ B : Set GeometricJet, IsOpen B ∧
--           CollarVelocity.jetSection F '' {p ∈ T | a p = 0} ⊆ B ∧
--           ∀ j ∈ B, jetNormal j ≠ 0 ∧ e₁ j = normalize (jetNormal j)) ∧
--         ∃ sLo sHi D : ℝ, 0 < sLo ∧ 0 < sHi ∧ 0 ≤ D ∧
--         ∀ ε : ℝ, 0 < ε → ∃ V : Set Base, IsOpen V ∧ {p ∈ T | a p = 0} ⊆ V ∧
--         ∀ (K P : Set Base), IsCompact K → K ⊆ T → (∀ p ∈ K, 0 < a p) →
--           P.Finite → P ⊆ K →
--           (∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
--             ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
--               fderiv ℝ f p (0,1) ≠ 0) →
--         ∀ H : ℝ, 0 ≤ H → ∃ Z : TopologicalSpace.Opens GeometricJet,
--           CollarVelocity.jetSection F '' T ⊆ Z ∧ (Z : Set GeometricJet) ⊆ Ω ∧
--         ∃ l : Loop (jetDomain Z),
--           (∀ J, l.amplitude J = a (decode J).1) ∧
--           (∃ W : Set GeometricJet, IsOpen W ∧
--             CollarVelocity.jetSection F '' {p ∈ T | a p = 0} ⊆ W ∧
--             ∀ J, decode J ∈ W → a (decode J).1 = 0 → ∀ t, l.velocity (J,t) = normal J) ∧
--           ∃ α : GeometricJet × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
--             (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
--             (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J).1) •
--               direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
--             (∀ x ∈ V, ∀ t, |α (CollarVelocity.jetSection F x,t)| < ε) ∧
--             (∀ x ∈ T, ∀ t : ℝ,
--               let J := surfaceCircularProfile F a e₁ e₂ α (x,t)
--               J ∈ regularBoundaryProfiles ∧ sLo ≤ profileCoefficients J 0 ∧
--                 profileCoefficients J 0 ≤ sHi ∧ |profileCoefficients J 1| ≤ D) ∧
--             ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
--               profileCoefficients (surfaceCircularProfile F a e₁ e₂ α (x,t)) 3 = 0 →
--                 H+2 < |profileCoefficients (surfaceCircularProfile F a e₁ e₂ α (x,t)) 2|
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.NormalFrame.Vec` and `OAI.ClosedSurfaceR4.TransverseSmallFunction.Base` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.CollarVelocity.JetBase`, `OAI.ClosedSurfaceR4.CollarVelocity.jetSection`, `OAI.ClosedSurfaceR4.PhaseGeometry.coordinateMetricHessian`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.RealTwoJet`, `OAI.ClosedSurfaceR4.RealModes.realSecondForm`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.normal` and `OAI.ClosedSurfaceR4.VelocityFrame.normalize` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.GeometryPreservation.BoundaryProfile` and `OAI.ClosedSurfaceR4.VelocityFrame.velocityRadius` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.VelocityFrame.direction` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.GeometryPreservation.profileCoefficients`, `OAI.ClosedSurfaceR4.GeometryPreservation.regularBoundaryProfiles` and `OAI.ClosedSurfaceR4.RealModes.inducedCoordinateMetric` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.SurfaceJetCoordinates.decode`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.GeometricJet`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.jetDomain`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.jetNormal` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.supportedJetDomain` (definitions bundle `OAIQ249SI009` of this split); `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.surfaceCircularProfile` (definitions bundle `OAIQ249SI011` of this split).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_supported_curve_crossing_loop` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Whitney/ActualSurfaceCollarProfiles.lean (declaration OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_surface_collar_profile_family)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_OAIQ249SI011

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry SurfaceJetCoordinates GeometryPreservation

theorem actual_surface_collar_profile_family {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {T U : Set Base} (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ F p))
    (hN : ∀ p ∈ U, coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧
      n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy)
    (haT : ∀ p ∈ T, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 → realSecondForm F dy dy p ≠ 0 ∧
      normalize (realSecondForm F dy dy p) ≠ -n p)
    :
    ∃ Ω : TopologicalSpace.Opens GeometricJet, CollarVelocity.jetSection F '' T ⊆ Ω ∧
      (Ω : Set GeometricJet) ⊆ supportedJetDomain U n a ∧
      ∃ e₁ e₂ : GeometricJet → Vec,
        ContDiffOn ℝ ∞ e₁ Ω ∧ ContDiffOn ℝ ∞ e₂ Ω ∧
        (∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
          j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0) ∧
      (∃ B : Set GeometricJet, IsOpen B ∧
        CollarVelocity.jetSection F '' {p ∈ T | a p = 0} ⊆ B ∧
        ∀ j ∈ B, jetNormal j ≠ 0 ∧ e₁ j = normalize (jetNormal j)) ∧
      ∃ sLo sHi D : ℝ, 0 < sLo ∧ 0 < sHi ∧ 0 ≤ D ∧
      ∀ ε : ℝ, 0 < ε → ∃ V : Set Base, IsOpen V ∧ {p ∈ T | a p = 0} ⊆ V ∧
      ∀ (K P : Set Base), IsCompact K → K ⊆ T → (∀ p ∈ K, 0 < a p) →
        P.Finite → P ⊆ K →
        (∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
          ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
            fderiv ℝ f p (0,1) ≠ 0) →
      ∀ H : ℝ, 0 ≤ H → ∃ Z : TopologicalSpace.Opens GeometricJet,
        CollarVelocity.jetSection F '' T ⊆ Z ∧ (Z : Set GeometricJet) ⊆ Ω ∧
      ∃ l : Loop (jetDomain Z),
        (∀ J, l.amplitude J = a (decode J).1) ∧
        (∃ W : Set GeometricJet, IsOpen W ∧
          CollarVelocity.jetSection F '' {p ∈ T | a p = 0} ⊆ W ∧
          ∀ J, decode J ∈ W → a (decode J).1 = 0 → ∀ t, l.velocity (J,t) = normal J) ∧
        ∃ α : GeometricJet × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
          (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
          (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J).1) •
            direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
          (∀ x ∈ V, ∀ t, |α (CollarVelocity.jetSection F x,t)| < ε) ∧
          (∀ x ∈ T, ∀ t : ℝ,
            let J := surfaceCircularProfile F a e₁ e₂ α (x,t)
            J ∈ regularBoundaryProfiles ∧ sLo ≤ profileCoefficients J 0 ∧
              profileCoefficients J 0 ≤ sHi ∧ |profileCoefficients J 1| ≤ D) ∧
          ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
            profileCoefficients (surfaceCircularProfile F a e₁ e₂ α (x,t)) 3 = 0 →
              H+2 < |profileCoefficients (surfaceCircularProfile F a e₁ e₂ α (x,t)) 2| := by
  sorry

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end
