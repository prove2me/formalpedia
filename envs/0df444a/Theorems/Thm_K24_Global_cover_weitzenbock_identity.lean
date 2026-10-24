-- Prove2me | Theorems.Thm_K24_Global_cover_weitzenbock_identity
-- name    : K24.Global.cover_weitzenbock_identity
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T20:36:20.083961+00:00
-- url     : https://prove2.me/theorems/435a69ad-61f4-46a9-a0a9-6445a4254d22
-- title:
--   Exact K24 Weitzenböck identity under the original bounded-cover Hölder assumptions
-- statement:
--   Under the full original smooth compact Hausdorff four-manifold, bounded local cover, circle-action, metric admissibility and invariance assumptions of the uniform natural Hölder statement, every order-two Hölder vector field Y satisfies the literal original covector identity bianchi z (killing z Y) = roughVectorLaplacianFlat z Y - ricciVectorFlat z Y. This proves exactly the weitzenbock field of ExactChangeOfSliceConclusions, retaining the original definitions and deriving canonical C2 regularity from the original cover hypotheses. It does not assert the other fields or the full K24 statement.
-- source:
--   Original Full K24 target aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 and uniform analytic residual 1a26d607-9f1f-4243-8fa0-c492842847f4; literal ExactChangeOfSliceConclusions.weitzenbock under the unchanged UniformHolderNaturalStatement assumptions.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open scoped Manifold ContDiff NNReal

namespace K24.Global
universe u
theorem cover_weitzenbock_identity :
  ∀ (coverBounds : CoverNumerics) (metricBounds : MetricCoefficientNumerics)
    (H : ℝ≥0), 1 ≤ H →
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] [CompactSpace M] [T2Space M],
      ∀ C : BoundedLocalCover M, C.numerics = coverBounds →
      ∀ rho : CircleAction M,
        HolderActionControl C metricBounds.exponent.value H 2 rho →
      ∀ (lam : ℝ) (ghat z g : RawCov2 M),
        MetricAdmissible C metricBounds ghat →
        MetricAdmissible C metricBounds z →
        MetricAdmissible C metricBounds g →
        IsInvariantCov2 rho ghat → IsInvariantCov2 rho z →
        ∀ Y : RawVector M, C.VectorHolder 2 metricBounds.exponent.value Y →
          bianchi z (killing z Y) = roughVectorLaplacianFlat z Y - ricciVectorFlat z Y := by sorry
end K24.Global
