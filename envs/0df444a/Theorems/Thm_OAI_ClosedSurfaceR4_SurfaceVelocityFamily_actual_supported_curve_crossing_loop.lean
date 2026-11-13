-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_actual_supported_curve_crossing_loop
-- name    : OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_supported_curve_crossing_loop
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:35:27.800942+00:00
-- url     : https://prove2.me/theorems/5e6580ee-09c5-49da-90dd-d86275574c0b
-- title:
--   OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_supported_curve_crossing_loop: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_supported_curve_crossing_loop` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/SurfaceCurveCrossingLoop.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/SurfaceCurveCrossingLoop.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.SurfaceVelocityFamily`, with `open Set Filter`, `open scoped ContDiff Topology Matrix`, `open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation CollarVelocity PhaseGeometry SurfaceJetCoordinates`):
--
--   ```lean
--   theorem actual_supported_curve_crossing_loop {F n : Base → Vec} {a : Base → ℝ}
--       (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
--       {T U : Set Base} (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
--       (hn : ContDiffOn ℝ ∞ n U)
--       (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ F p))
--       (hN : ∀ p ∈ U, coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧ n p ⬝ᵥ n p = 1)
--       (hHess : ∀ p ∈ U, 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy)
--       (haT : ∀ p ∈ T, 0 ≤ a p)
--       (hboundary : ∀ p ∈ T, a p = 0 → realSecondForm F dy dy p ≠ 0 ∧
--         normalize (realSecondForm F dy dy p) ≠ -n p)
--       {K : ι → Set Base} (hK : ∀ i, IsCompact (K i)) (hKT : ∀ i, K i ⊆ T)
--       {P : Set Base} (hP : P.Finite)
--       (hlocal : ∀ p ∈ (⋃ i, K i) \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
--         ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ (⋃ i, K i) ∩ N, f x = 0) ∧
--           fderiv ℝ f p (0,1) ≠ 0)
--       {E : Set Base} (hE : E.Finite) (hET : E ⊆ T) (haE : ∀ x ∈ E, 0 < a x)
--       (slopeBound : ℝ) (hSlope : 0 ≤ slopeBound)
--       {b c k : ι → Base → ℝ}
--       (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
--       (hk : ∀ i, ContDiff ℝ ∞ (k i))
--       (hbc : ∀ i, ∀ x ∈ K i, b i x ≠ 0 ∨ c i x ≠ 0)
--       (B : ℝ) (hB : 0 ≤ B) (hkb : ∀ i, ∀ x ∈ K i, -B ≤ k i x)
--       (hold : ∀ i, ∀ x ∈ K i, a x = 0 →
--         0 < ((coordDeriv dy (coordDeriv dx F) x ⬝ᵥ normalize (realSecondForm F dy dy x))*b i x +
--           Real.sqrt (realSecondForm F dy dy x ⬝ᵥ realSecondForm F dy dy x)*c i x)^2 + k i x*(b i x)^2) :
--       ∃ Z : TopologicalSpace.Opens GeometricJet,
--         jetSection F '' T ⊆ Z ∧ (Z : Set GeometricJet) ⊆ supportedJetDomain U n a ∧
--       ∃ l : Loop (jetDomain Z),
--         (∀ J, l.amplitude J = a (decode J).1) ∧
--         (∃ W : Set GeometricJet, IsOpen W ∧ jetSection F '' {p ∈ T | a p = 0} ⊆ W ∧
--           ∀ J, decode J ∈ W → a (decode J).1 = 0 → ∀ t, l.velocity (J,t) = normal J) ∧
--       ∃ e₁ e₂ : GeometricJet → Vec, ∃ α : GeometricJet × ℝ → ℝ,
--         ContDiffOn ℝ ∞ e₁ Z ∧ ContDiffOn ℝ ∞ e₂ Z ∧ ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
--         (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
--         (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J).1) •
--           direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
--       (∀ x ∈ T, ∀ t : ℝ, surfaceCircularProfile F a e₁ e₂ α (x,t) ∈ regularBoundaryProfiles) ∧
--       ∃ η : ℝ, 0 < η ∧
--         (∀ z : ℝ, 0 < z → z < η →
--         ∀ i, ∀ x ∈ K i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ p : Base,
--         ‖realBoundaryProfile G z p-surfaceCircularProfile F a e₁ e₂ α (x,t)‖ < η →
--         k i x ≤ coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p →
--         realSecondForm G (b i x,c i x) (b i x,c i x) p ≠ 0 ∧
--         normalize (realSecondForm G (b i x,c i x) (b i x,c i x) p) ≠
--           -profilePreferred (realBoundaryProfile G z p)) ∧
--         ∀ z : ℝ, 0 < z → z < η → ∀ x ∈ E, ∀ t ∈ Icc (0 : ℝ) 1,
--         ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ p : Base,
--         ‖realBoundaryProfile G z p-surfaceCircularProfile F a e₁ e₂ α (x,t)‖ < η →
--         ∀ κ : ℝ,
--         coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p =
--           κ*gramDet (coordDeriv dx G p) (coordDeriv dy G p) →
--         -B ≤ coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p →
--         ∀ r s : ℝ, |r| ≤ slopeBound → |s| ≤ slopeBound →
--           0 < orderedCrossing G (1,r) (1,s) p κ ∧
--           0 < orderedCrossing G (1,s) (1,r) p κ ∧
--           ((0 < realSecondForm G (1,r) (1,r) p ⬝ᵥ profilePreferred (realBoundaryProfile G z p) ∧
--             0 < realSecondForm G (1,s) (1,s) p ⬝ᵥ profilePreferred (realBoundaryProfile G z p)) ∨
--            (0 < realSecondForm G (1,r) (1,r) p ⬝ᵥ realSecondForm G (1,s) (1,s) p ∧
--              ∃ w : Vec, profilePreferred (realBoundaryProfile G z p) ⬝ᵥ w = 0 ∧
--                0 < realSecondForm G (1,r) (1,r) p ⬝ᵥ w ∧
--                0 < realSecondForm G (1,s) (1,s) p ⬝ᵥ w))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.NormalFrame.Vec`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet` and `OAI.ClosedSurfaceR4.TransverseSmallFunction.Base` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.CollarVelocity.JetBase`, `OAI.ClosedSurfaceR4.CollarVelocity.jetSection`, `OAI.ClosedSurfaceR4.PhaseGeometry.coordinateMetricHessian`, `OAI.ClosedSurfaceR4.RealModes.RField`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.RealTwoJet`, `OAI.ClosedSurfaceR4.RealModes.realMetric`, `OAI.ClosedSurfaceR4.RealModes.realSecondForm`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.normal` and `OAI.ClosedSurfaceR4.VelocityFrame.normalize` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.GeometryPreservation.BoundaryProfile` and `OAI.ClosedSurfaceR4.VelocityFrame.velocityRadius` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.VelocityFrame.direction` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.GeometryPreservation.profilePreferred`, `OAI.ClosedSurfaceR4.GeometryPreservation.realBoundaryProfile`, `OAI.ClosedSurfaceR4.GeometryPreservation.regularBoundaryProfiles` and `OAI.ClosedSurfaceR4.RealModes.inducedCoordinateMetric` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.SurfaceJetCoordinates.decode`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.GeometricJet`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.jetDomain` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.supportedJetDomain` (definitions bundle `OAIQ249SI009` of this split); `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.surfaceCircularProfile` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.RealModes.coordinateGauss` and `OAI.ClosedSurfaceR4.VelocityFrame.orderedCrossing` (definitions bundle `OAIQ249SI013` of this split).
--
--   **Used by.** The proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_constructed_circular_primitive_boundary` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_preserving_circular_primitive_boundary` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/SurfaceCurveCrossingLoop.lean (declaration OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_supported_curve_crossing_loop)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_OAIQ249SI011

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation CollarVelocity PhaseGeometry SurfaceJetCoordinates

variable {ι : Type*} [Finite ι]

theorem actual_supported_curve_crossing_loop {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {T U : Set Base} (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ F p))
    (hN : ∀ p ∈ U, coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧ n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy)
    (haT : ∀ p ∈ T, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 → realSecondForm F dy dy p ≠ 0 ∧
      normalize (realSecondForm F dy dy p) ≠ -n p)
    {K : ι → Set Base} (hK : ∀ i, IsCompact (K i)) (hKT : ∀ i, K i ⊆ T)
    {P : Set Base} (hP : P.Finite)
    (hlocal : ∀ p ∈ (⋃ i, K i) \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ (⋃ i, K i) ∩ N, f x = 0) ∧
        fderiv ℝ f p (0,1) ≠ 0)
    {E : Set Base} (hE : E.Finite) (hET : E ⊆ T) (haE : ∀ x ∈ E, 0 < a x)
    (slopeBound : ℝ) (hSlope : 0 ≤ slopeBound)
    {b c k : ι → Base → ℝ}
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (hk : ∀ i, ContDiff ℝ ∞ (k i))
    (hbc : ∀ i, ∀ x ∈ K i, b i x ≠ 0 ∨ c i x ≠ 0)
    (B : ℝ) (hB : 0 ≤ B) (hkb : ∀ i, ∀ x ∈ K i, -B ≤ k i x)
    (hold : ∀ i, ∀ x ∈ K i, a x = 0 →
      0 < ((coordDeriv dy (coordDeriv dx F) x ⬝ᵥ normalize (realSecondForm F dy dy x))*b i x +
        Real.sqrt (realSecondForm F dy dy x ⬝ᵥ realSecondForm F dy dy x)*c i x)^2 + k i x*(b i x)^2) :
    ∃ Z : TopologicalSpace.Opens GeometricJet,
      jetSection F '' T ⊆ Z ∧ (Z : Set GeometricJet) ⊆ supportedJetDomain U n a ∧
    ∃ l : Loop (jetDomain Z),
      (∀ J, l.amplitude J = a (decode J).1) ∧
      (∃ W : Set GeometricJet, IsOpen W ∧ jetSection F '' {p ∈ T | a p = 0} ⊆ W ∧
        ∀ J, decode J ∈ W → a (decode J).1 = 0 → ∀ t, l.velocity (J,t) = normal J) ∧
    ∃ e₁ e₂ : GeometricJet → Vec, ∃ α : GeometricJet × ℝ → ℝ,
      ContDiffOn ℝ ∞ e₁ Z ∧ ContDiffOn ℝ ∞ e₂ Z ∧ ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
      (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
      (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J).1) •
        direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
    (∀ x ∈ T, ∀ t : ℝ, surfaceCircularProfile F a e₁ e₂ α (x,t) ∈ regularBoundaryProfiles) ∧
    ∃ η : ℝ, 0 < η ∧
      (∀ z : ℝ, 0 < z → z < η →
      ∀ i, ∀ x ∈ K i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ p : Base,
      ‖realBoundaryProfile G z p-surfaceCircularProfile F a e₁ e₂ α (x,t)‖ < η →
      k i x ≤ coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p →
      realSecondForm G (b i x,c i x) (b i x,c i x) p ≠ 0 ∧
      normalize (realSecondForm G (b i x,c i x) (b i x,c i x) p) ≠
        -profilePreferred (realBoundaryProfile G z p)) ∧
      ∀ z : ℝ, 0 < z → z < η → ∀ x ∈ E, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ p : Base,
      ‖realBoundaryProfile G z p-surfaceCircularProfile F a e₁ e₂ α (x,t)‖ < η →
      ∀ κ : ℝ,
      coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p =
        κ*gramDet (coordDeriv dx G p) (coordDeriv dy G p) →
      -B ≤ coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p →
      ∀ r s : ℝ, |r| ≤ slopeBound → |s| ≤ slopeBound →
        0 < orderedCrossing G (1,r) (1,s) p κ ∧
        0 < orderedCrossing G (1,s) (1,r) p κ ∧
        ((0 < realSecondForm G (1,r) (1,r) p ⬝ᵥ profilePreferred (realBoundaryProfile G z p) ∧
          0 < realSecondForm G (1,s) (1,s) p ⬝ᵥ profilePreferred (realBoundaryProfile G z p)) ∨
         (0 < realSecondForm G (1,r) (1,r) p ⬝ᵥ realSecondForm G (1,s) (1,s) p ∧
           ∃ w : Vec, profilePreferred (realBoundaryProfile G z p) ⬝ᵥ w = 0 ∧
             0 < realSecondForm G (1,r) (1,r) p ⬝ᵥ w ∧
             0 < realSecondForm G (1,s) (1,s) p ⬝ᵥ w)) := by
  sorry

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end
