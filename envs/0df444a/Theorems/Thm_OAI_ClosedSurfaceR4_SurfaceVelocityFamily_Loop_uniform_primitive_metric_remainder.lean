-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_uniform_primitive_metric_remainder
-- name    : OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_metric_remainder
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:49:16.213889+00:00
-- url     : https://prove2.me/theorems/01337a70-deeb-4dbf-85c9-f0d703b4f326
-- title:
--   OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_metric_remainder: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_metric_remainder` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/PrimitiveTensorRemainder.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/PrimitiveTensorRemainder.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop`, with `open Set`, `open scoped ContDiff Matrix`, `open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates`):
--
--   ```lean
--   theorem uniform_primitive_metric_remainder {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a)
--       (hamp : l.HasSpatialAmplitude a) {S : TopologicalSpace.Opens JetPolynomial.Base}
--       {K : Set LowJet} (hK : IsCompact K) (hKO : K ⊆ O)
--       (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
--       (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
--       ∃ loss : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
--         ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
--           (hGK : MapsTo (lowJet G) S K) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
--         WeightedBound S s (m+(2*(n+1)+1)) B (lowJet G) →
--         let g := l.geometry G hG (fun _ hp => hKO (hGK hp))
--         ∀ U : ℕ → Family S Euclidean,
--           (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
--           (∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U i).val y.1 (y.2 : Period))) →
--           U 0 = g.initial → (g.yyCoefficient U 1).fluct = 0 →
--           (∀ r, 1 ≤ r → r ≤ n →
--             (g.xxCoefficient (coordinateVector 0) U r).fluct = 0 ∧
--             (g.xyCoefficient (coordinateVector 0) U r).fluct = 0 ∧
--             (g.yyCoefficient U (r+1)).fluct = 0) →
--         WeightedBound S z m (D*z^(n+1)/s^loss)
--           (fun p => RealModes.realMetricTensor
--             (spaceCoordinates ∘ finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q)) U ℓ (n+1) z ∘
--               planeCoordinateIsometry.symm) (planeCoordinateIsometry p)-
--             l.meanTensorOperator n z G (planeCoordinateIsometry p)-![a p^2,0,0])
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.CovarianceCorrector.Period`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.LowIndex`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.coordinateVector`, `OAI.ClosedSurfaceR4.JetPolynomial.lowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.planeCoordinateIsometry`, `OAI.ClosedSurfaceR4.JetVelocityCoordinates.Euclidean`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor` and `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realMetricTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.HasSpatialAmplitude` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.instAddCommGroupFamily` and `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.val` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.JetVelocityCoordinates.toEuclidean` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.fluct` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.geometry` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.finiteAnsatz`, `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.Represents`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.initial`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xxCoefficient`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xyCoefficient`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yyCoefficient`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.coefficientExpressions` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanTensorOperator` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.Space` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_phase_primitive_metric` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/PrimitiveTensorRemainder.lean (declaration OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_metric_remainder)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem uniform_primitive_metric_remainder {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (hamp : l.HasSpatialAmplitude a) {S : TopologicalSpace.Opens JetPolynomial.Base}
    {K : Set LowJet} (hK : IsCompact K) (hKO : K ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
    ∃ loss : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (hGK : MapsTo (lowJet G) S K) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s (m+(2*(n+1)+1)) B (lowJet G) →
      let g := l.geometry G hG (fun _ hp => hKO (hGK hp))
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
        (∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U i).val y.1 (y.2 : Period))) →
        U 0 = g.initial → (g.yyCoefficient U 1).fluct = 0 →
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.yyCoefficient U (r+1)).fluct = 0) →
      WeightedBound S z m (D*z^(n+1)/s^loss)
        (fun p => RealModes.realMetricTensor
          (spaceCoordinates ∘ finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q)) U ℓ (n+1) z ∘
            planeCoordinateIsometry.symm) (planeCoordinateIsometry p)-
          l.meanTensorOperator n z G (planeCoordinateIsometry p)-![a p^2,0,0]) := by
  sorry

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end
