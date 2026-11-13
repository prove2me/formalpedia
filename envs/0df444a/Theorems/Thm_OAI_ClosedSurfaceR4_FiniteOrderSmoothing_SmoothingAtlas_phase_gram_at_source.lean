-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phase_gram_at_source
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_gram_at_source
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:04:34.617762+00:00
-- url     : https://prove2.me/theorems/22d0576c-9630-4061-97d7-992201602df0
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_gram_at_source: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_gram_at_source` of [lean/OAI/Geometry/SurfaceImmersion/Atlas/PhaseExteriorDomain.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/PhaseExteriorDomain.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Filter Manifold`, `open scoped ContDiff Topology`, `open SurfaceJetCoordinates`):
--
--   ```lean
--   lemma phase_gram_at_source (i : A.centers)
--       (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
--       (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
--       {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
--       {p : M} (hp : p ∈ ((chart (i : M)).trans e).source) (hw : A.weight i p ≠ 0) :
--       NormalFrame.gramDet
--         (SmallModes.coordDeriv SmallModes.dx (A.phaseRealChartMap i e.symm F)
--           (baseEquiv (e (chart (i : M) p))))
--         (SmallModes.coordDeriv SmallModes.dy (A.phaseRealChartMap i e.symm F)
--           (baseEquiv (e (chart (i : M) p)))) ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.NormalFrame.Vec` and `OAI.ClosedSurfaceR4.NormalFrame.gramDet` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy` and `OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseRealChartMap` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.IsSmoothIsometricImmersion`, `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_circular_primitive_boundary_step`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.adapted_primitive_geometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_boundary_matching`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_phase_exterior_preservation`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_exterior_crossing_preservation` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.reference_circular_starting_family` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/PhaseExteriorDomain.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_gram_at_source)

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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

namespace SmoothingAtlas
variable [IsManifold planeModel ∞ M] [CompactSpace M] (A : SmoothingAtlas M)

lemma phase_gram_at_source (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {p : M} (hp : p ∈ ((chart (i : M)).trans e).source) (hw : A.weight i p ≠ 0) :
    NormalFrame.gramDet
      (SmallModes.coordDeriv SmallModes.dx (A.phaseRealChartMap i e.symm F)
        (baseEquiv (e (chart (i : M) p))))
      (SmallModes.coordDeriv SmallModes.dy (A.phaseRealChartMap i e.symm F)
        (baseEquiv (e (chart (i : M) p)))) ≠ 0 := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
