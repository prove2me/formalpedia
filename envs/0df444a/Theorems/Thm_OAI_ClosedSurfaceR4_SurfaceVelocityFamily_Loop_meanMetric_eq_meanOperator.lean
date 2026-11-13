-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_meanMetric_eq_meanOperator
-- name    : OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanMetric_eq_meanOperator
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:48:25.569203+00:00
-- url     : https://prove2.me/theorems/8deaf330-5f7c-4be7-ab47-223667eb5241
-- title:
--   OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanMetric_eq_meanOperator: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanMetric_eq_meanOperator` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/SurfacePrimitiveError.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/SurfacePrimitiveError.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop`, with `open Set`, `open scoped ContDiff`, `open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector`, `open WeightedEstimates`):
--
--   ```lean
--   lemma meanMetric_eq_meanOperator {a : Base → ℝ} (ha : l.HasSpatialAmplitude a)
--       {S : TopologicalSpace.Opens Base} {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
--       (hGO : MapsTo (lowJet G) S O) (n : ℕ) (b c : Bool) (z : ℝ)
--       (U : ℕ → Family S Euclidean)
--       (hU : ∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i))
--       {p : Base} (hp : p ∈ S) :
--       MetricPolynomial.meanMetric (l.geometry G hG hGO) (coordinateVector 0) U n b c z p =
--         l.meanOperator n b c z G p+(if b && c then a p^2 else 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.LowIndex`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.coordinateVector`, `OAI.ClosedSurfaceR4.JetPolynomial.lowJet` and `OAI.ClosedSurfaceR4.JetVelocityCoordinates.Euclidean` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.HasSpatialAmplitude` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.geometry` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.meanMetric`, `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.Represents`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.coefficientExpressions` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanOperator` (definitions bundle `OAIQ249SI012` of this split).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_metric_remainder` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/SurfacePrimitiveError.lean (declaration OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanMetric_eq_meanOperator)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity
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
open scoped ContDiff
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector
open WeightedEstimates

variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

lemma meanMetric_eq_meanOperator {a : Base → ℝ} (ha : l.HasSpatialAmplitude a)
    {S : TopologicalSpace.Opens Base} {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) (n : ℕ) (b c : Bool) (z : ℝ)
    (U : ℕ → Family S Euclidean)
    (hU : ∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i))
    {p : Base} (hp : p ∈ S) :
    MetricPolynomial.meanMetric (l.geometry G hG hGO) (coordinateVector 0) U n b c z p =
      l.meanOperator n b c z G p+(if b && c then a p^2 else 0) := by
  sorry

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end
