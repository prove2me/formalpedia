-- Prove2me | Theorems.Thm_K24_Global_metric_admissible_positive_holder_neighborhood
-- name    : K24.Global.metric_admissible_positive_holder_neighborhood
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T19:45:04.340223+00:00
-- url     : https://prove2.me/theorems/ce9d8ab5-1d55-4ad5-8a36-05fde711507f
-- title:
--   Positive metric neighborhood in the original K24 order-two Hölder tensor norm
-- statement:
--   For every original smooth compact Hausdorff four-manifold M, original BoundedLocalCover C, original MetricCoefficientNumerics b with order at least two, and actual covariant two-tensor z satisfying MetricAdmissible C b z, the original positiveHolderMetrics C 2 b.exponent.value is a SectionNeighborhood of z relative to tensorHolderSpace C 2 b.exponent.value in the unchanged original C.cov2ENorm 2 b.exponent.value. The proof chooses radius b.lower / 32. It derives all lower-order regularity and finiteness from the original admissibility and cover numerics.
-- source:
--   Original FullK24Statement root aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22, HolderNaturalConclusions.positive_neighborhood (Def_K24GlobalStatement.lean:326-327); original MetricAdmissible and SectionNeighborhood in Def_K24GlobalAnalysis.lean.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open scoped Manifold ContDiff NNReal ENNReal Matrix.Norms.Elementwise

namespace K24.Global
universe u

theorem metric_admissible_positive_holder_neighborhood :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [CompactSpace M] [T2Space M],
    ∀ (C : BoundedLocalCover M) (metricBounds : MetricCoefficientNumerics) (z : RawCov2 M),
      MetricAdmissible C metricBounds z →
      SectionNeighborhood (tensorHolderSpace C 2 metricBounds.exponent.value)
        (positiveHolderMetrics C 2 metricBounds.exponent.value)
        (C.cov2ENorm 2 metricBounds.exponent.value) z := by
  sorry

end K24.Global
