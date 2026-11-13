-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_meanTensorPolynomial_global_extension
-- name    : OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanTensorPolynomial_global_extension
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:48:31.11325+00:00
-- url     : https://prove2.me/theorems/11c9bb94-ed6b-4d3f-b234-23721e9b48d3
-- title:
--   OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanTensorPolynomial_global_extension: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanTensorPolynomial_global_extension` of [lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPrimitivePolynomial.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPrimitivePolynomial.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators`, `open JetPolynomial JetPolynomial.Perturbation`):
--
--   ```lean
--   lemma meanTensorPolynomial_global_extension {Q : Set LowJet} (hQ : IsCompact Q)
--       (hQO : Q ⊆ O) (n : ℕ) :
--       ∃ P : Fin 3 → Fin n → Expression,
--         (∀ k r, (P k r).SmoothCoeffs univ) ∧
--         (∀ k r, (P k r).order = (l.meanTensorPolynomial n k r).order) ∧
--         (∀ k r, (P k r).loss = (l.meanTensorPolynomial n k r).loss) ∧
--         ∀ (G : JetPolynomial.Base → JetPolynomial.Space), ContDiff ℝ ∞ G →
--           ∀ (z : ℝ) (p : JetPolynomial.Base), lowJet G p ∈ Q →
--           coordinateMetricMap P z G (planeCoordinateIsometry p) =
--             l.meanTensorOperator n z G (planeCoordinateIsometry p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowIndex`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.lowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.planeCoordinateIsometry`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression.SmoothCoeffs`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss` and `OAI.ClosedSurfaceR4.JetPolynomial.Expression.order` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinateMetricMap` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanTensorOperator` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanTensorPolynomial` (definitions bundle `OAIQ249SI012` of this split).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_phase_primitive_metric` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPrimitivePolynomial.lean (declaration OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanTensorPolynomial_global_extension)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_OAIQ249SI012

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetPolynomial.Perturbation
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

lemma meanTensorPolynomial_global_extension {Q : Set LowJet} (hQ : IsCompact Q)
    (hQO : Q ⊆ O) (n : ℕ) :
    ∃ P : Fin 3 → Fin n → Expression,
      (∀ k r, (P k r).SmoothCoeffs univ) ∧
      (∀ k r, (P k r).order = (l.meanTensorPolynomial n k r).order) ∧
      (∀ k r, (P k r).loss = (l.meanTensorPolynomial n k r).loss) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space), ContDiff ℝ ∞ G →
        ∀ (z : ℝ) (p : JetPolynomial.Base), lowJet G p ∈ Q →
        coordinateMetricMap P z G (planeCoordinateIsometry p) =
          l.meanTensorOperator n z G (planeCoordinateIsometry p) := by
  sorry

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end
