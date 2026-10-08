-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_smooth_isometric_immersion
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:26.941689+00:00
-- url     : https://prove2.me/theorems/43c7ce40-2403-4db8-8117-4fecbe089c6f
-- statement:
--   The theorem states that, for every compact, Hausdorff, second-countable topological space M equipped with a charted-space structure modeled on the Euclidean plane ℝ² and a smooth (C^∞) manifold structure, and for every smooth Riemannian metric g on M (a C^∞ family of inner products on the tangent spaces, with respect to the plane model), there exists a map F from M to Euclidean four-space ℝ⁴ that is a smooth isometric immersion with respect to g. Here this means that F is C^∞ as a map between manifolds, and that for every point p and all tangent vectors v and w at p, the Euclidean inner product of the derivatives dF_p(v) and dF_p(w) in ℝ⁴ equals g_p(v,w). In particular, no separate injectivity or embedding requirement is stated beyond this isometry condition on the differential.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SurfaceImmersion.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SurfaceImmersion.lean; bytes 1055..1294
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SurfaceImmersion

namespace OAI

noncomputable section

open Bundle Manifold

open scoped ContDiff

namespace ClosedSurfaceR4

namespace FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [SecondCountableTopology M]

/-- Every compact smooth Riemannian surface admits a smooth isometric immersion into Euclidean four-space. -/
theorem smooth_isometric_immersion (g : SmoothMetric M) :
    ∃ F : M → Space, IsSmoothIsometricImmersion M g F := by
  sorry

end FiniteOrderSmoothing
end ClosedSurfaceR4
end
end OAI
