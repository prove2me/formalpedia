-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_profiled_phase_primitive_realization
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_profiled_phase_primitive_realization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:08:24.720496+00:00
-- url     : https://prove2.me/theorems/13891c79-8b92-4765-a9bb-221a7a0d7be0
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_profiled_phase_primitive_realization (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_profiled_phase_primitive_realization` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/IndependentProfiledPhase.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/IndependentProfiledPhase.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology`, `open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector WeightedEstimates`, `open PrimitiveRealization`):
--
--   ```lean
--   theorem independent_profiled_phase_primitive_realization (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
--       (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
--       (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
--       (i : A₀.centers)
--       (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
--       (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
--       {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
--       (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
--       (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
--       {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
--       {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude a)
--       (S : TopologicalSpace.Opens JetPolynomial.Base)
--       (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
--       {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
--       (hFQ : MapsTo (lowJet (A₀.jetChartMap i F ∘ e.symm)) S Q)
--       (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
--       (hKA : e.symm '' K ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base))
--       (hone : ∀ x ∈ e.symm '' K, χ x = 1)
--       (hv : ∀ J ∈ O, lowJetPosition J ∉ K → ∀ t, l.velocity (J,t) = SurfaceVelocityFamily.normal J)
--       (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
--       (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)
--       :
--       ∃ c cB V₀ : ℝ, 0 < c ∧ 0 < cB ∧ 0 ≤ V₀ ∧ ∀ R N : ℕ,
--       ∃ lp : ℕ, ∃ (b u η L C Cv Dp : ℝ) (P : ℕ → ℝ), 0 ≤ b ∧ b < 1/16 ∧ 0 < u ∧
--         0 < η ∧ η ≤ 1 ∧ 0 ≤ L ∧ 0 ≤ C ∧ 0 ≤ Cv ∧ 0 ≤ Dp ∧
--         b < 1/(1+(lp : ℝ)) ∧ (∀ m, 0 ≤ P m) ∧
--         ∀ z : ℝ, 0 < z → z < η → ∃ G V : M → Space,
--           ContMDiff planeModel spaceModel ∞ G ∧ ContMDiff planeModel spaceModel ∞ V ∧
--           A₀.WeightedBound 1 3 (L*z^u) (G-F) ∧
--           (∀ m, A₀.ShiftedBound 2 m (z^b) (P m) G) ∧
--           A₀.WeightedBound z R Cv V ∧
--           A₀.WeightedBound 1 0 V₀ V ∧
--           A₀.ShiftedBound 2 R z (Cv/z^2) V ∧
--           A₀.TensorWeightedBound 1 R (C*z^N)
--             (inducedTensor V-(g.inner+A₀.bundleRestore A₀.tensorTriv i
--               (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![a q^2,0,0]) y)))) ∧
--           (∀ p, Function.Injective (mfderiv planeModel spaceModel V p)) ∧
--           (∀ p, ∃ v w : SmallModes.Base,
--             RealModes.realSecondForm (coordinateMap V p) v w (coordinateCenter p) ≠ 0) ∧
--           (∀ j x, x ∈ (modeSupport (data.A.chartWeightCompact j) : Set SmallModes.Base) →
--             cB < ‖RealModes.realSecondTensor (spaceCoordinates ∘ data.A.vectorPlaneRead j V) x‖) ∧
--           (∀ p ∈ (S : Set JetPolynomial.Base) ∩ e.target,
--             let H := SurfaceVelocityFamily.Loop.primitiveNormalTriple (A₀.vectorChartRead i V ∘ e.symm) p
--             NormalFrame.gramDet (H 0) (H 1) ≠ 0 ∧
--               c < ‖RealModes.realNormalPart (H 0) (H 1) (H 2)‖) ∧
--           (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
--           (∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G) ∧
--           ∃ hGs : ContMDiff planeModel spaceModel ∞ G,
--           ∃ hGO : MapsTo (lowJet (A₀.jetChartMap i G ∘ e.symm)) S O,
--             ∀ p ∈ (S : Set JetPolynomial.Base) ∩ e.target,
--               let geom := l.geometry (A₀.jetChartMap i G ∘ e.symm)
--                 ((A₀.jetChartMap_smooth i hGs).comp hi) hGO
--               let t : Period := ((ℓ p/z : ℝ) : Period)
--               ‖SurfaceVelocityFamily.Loop.primitiveJetProfile
--                   (A₀.vectorChartRead i V ∘ e.symm) z p-
--                 ![geom.longitudinal.val p t,geom.Y p,geom.C p,
--                   (geom.longitudinal.slow (coordinateVector 1)).val p t,geom.V.angle.val p t]‖ ≤
--                 Dp*z/(z^b)^lp
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.CovarianceCorrector.Period`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualSmul`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.LowIndex`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.coordinateVector`, `OAI.ClosedSurfaceR4.JetPolynomial.lowJet`, `OAI.ClosedSurfaceR4.JetVelocityCoordinates.Euclidean`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.bundleRestore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.coordinateMap`, `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.fiberFromThree`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inducedTensor`, `OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realNormalPart`, `OAI.ClosedSurfaceR4.RealModes.realSecondForm`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.normal`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorChartRead`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.HasSpatialAmplitude` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.ShiftedBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` and `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.val` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.VelocityFrame.NormalTriple` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap_smooth` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.coordinateCenter`, `OAI.ClosedSurfaceR4.JetPolynomial.localizedTensorPullback`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseSurfaceSupport` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.primitiveJetProfile` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independentProfiledPhaseDualAdd`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independentProfiledPhaseFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independentProfiledPhaseFiberSpace` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.primitiveNormalTriple` (definitions bundle `OAIQ249SI009` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.angle`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.slow`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.longitudinal` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.geometry` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_phase_primitive_five_profiles`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_exact_profiled_phase_primitive_metric` and `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_profiled_phase_primitive_fast_family` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/IndependentProfiledPhase.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_profiled_phase_primitive_realization)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI009
import Definitions.Def_OAIQ249SI010

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace MetricGoodPhaseData
open PrimitiveRealization
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independentProfiledPhaseDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independentProfiledPhaseFiberSpace
local instance independentProfiledPhaseDualSmul_r6f212a_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independentProfiledPhaseFiberNormed
local instance independentProfiledPhaseSectionNormed_r6f212a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independentProfiledPhaseSectionSpace_r6f212a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem independent_profiled_phase_primitive_realization (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : A₀.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude a)
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (hFQ : MapsTo (lowJet (A₀.jetChartMap i F ∘ e.symm)) S Q)
    (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
    (hKA : e.symm '' K ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base))
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (hv : ∀ J ∈ O, lowJetPosition J ∉ K → ∀ t, l.velocity (J,t) = SurfaceVelocityFamily.normal J)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)
    :
    ∃ c cB V₀ : ℝ, 0 < c ∧ 0 < cB ∧ 0 ≤ V₀ ∧ ∀ R N : ℕ,
    ∃ lp : ℕ, ∃ (b u η L C Cv Dp : ℝ) (P : ℕ → ℝ), 0 ≤ b ∧ b < 1/16 ∧ 0 < u ∧
      0 < η ∧ η ≤ 1 ∧ 0 ≤ L ∧ 0 ≤ C ∧ 0 ≤ Cv ∧ 0 ≤ Dp ∧
      b < 1/(1+(lp : ℝ)) ∧ (∀ m, 0 ≤ P m) ∧
      ∀ z : ℝ, 0 < z → z < η → ∃ G V : M → Space,
        ContMDiff planeModel spaceModel ∞ G ∧ ContMDiff planeModel spaceModel ∞ V ∧
        A₀.WeightedBound 1 3 (L*z^u) (G-F) ∧
        (∀ m, A₀.ShiftedBound 2 m (z^b) (P m) G) ∧
        A₀.WeightedBound z R Cv V ∧
        A₀.WeightedBound 1 0 V₀ V ∧
        A₀.ShiftedBound 2 R z (Cv/z^2) V ∧
        A₀.TensorWeightedBound 1 R (C*z^N)
          (inducedTensor V-(g.inner+A₀.bundleRestore A₀.tensorTriv i
            (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![a q^2,0,0]) y)))) ∧
        (∀ p, Function.Injective (mfderiv planeModel spaceModel V p)) ∧
        (∀ p, ∃ v w : SmallModes.Base,
          RealModes.realSecondForm (coordinateMap V p) v w (coordinateCenter p) ≠ 0) ∧
        (∀ j x, x ∈ (modeSupport (data.A.chartWeightCompact j) : Set SmallModes.Base) →
          cB < ‖RealModes.realSecondTensor (spaceCoordinates ∘ data.A.vectorPlaneRead j V) x‖) ∧
        (∀ p ∈ (S : Set JetPolynomial.Base) ∩ e.target,
          let H := SurfaceVelocityFamily.Loop.primitiveNormalTriple (A₀.vectorChartRead i V ∘ e.symm) p
          NormalFrame.gramDet (H 0) (H 1) ≠ 0 ∧
            c < ‖RealModes.realNormalPart (H 0) (H 1) (H 2)‖) ∧
        (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
        (∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G) ∧
        ∃ hGs : ContMDiff planeModel spaceModel ∞ G,
        ∃ hGO : MapsTo (lowJet (A₀.jetChartMap i G ∘ e.symm)) S O,
          ∀ p ∈ (S : Set JetPolynomial.Base) ∩ e.target,
            let geom := l.geometry (A₀.jetChartMap i G ∘ e.symm)
              ((A₀.jetChartMap_smooth i hGs).comp hi) hGO
            let t : Period := ((ℓ p/z : ℝ) : Period)
            ‖SurfaceVelocityFamily.Loop.primitiveJetProfile
                (A₀.vectorChartRead i V ∘ e.symm) z p-
              ![geom.longitudinal.val p t,geom.Y p,geom.C p,
                (geom.longitudinal.slow (coordinateVector 1)).val p t,geom.V.angle.val p t]‖ ≤
              Dp*z/(z^b)^lp := by
  sorry

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
