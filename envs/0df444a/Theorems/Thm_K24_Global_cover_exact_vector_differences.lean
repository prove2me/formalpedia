-- Prove2me | Theorems.Thm_K24_Global_cover_exact_vector_differences
-- name    : K24.Global.cover_exact_vector_differences
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-26T04:28:05.525558+00:00
-- url     : https://prove2.me/theorems/e20a49d2-9208-4271-ab75-f1c32b79f983
-- title:
--   Exact K24 center and actual metric vector differences from the original assumptions
-- statement:
--   Under the unchanged original uniform natural Holder geometric hypotheses, every original order-two Holder vector field satisfies both literal projected vector difference identities. The center identity is projected Bianchi subtraction; the actual-metric identity retains both terms of actualMetricVectorDefect for arbitrary admissible g, with no invariance of g and no added regularity or Haar-integrability premise. CT and CV are present in the original prefix and do not occur in these two identities. This result does not assert the full analytic core or FullK24Statement.
-- source:
--   Original full root aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22; analytic core 3db797ab-2b53-4cda-b318-e4780235e38c; literal ExactChangeOfSliceConclusions.center_vector_difference and actual_vector_difference under the UniformHolderNaturalStatement prefix.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open scoped NNReal ENNReal Manifold ContDiff

namespace K24.Global
universe u
theorem cover_exact_vector_differences :
  ∀ (coverBounds : CoverNumerics) (metricBounds : MetricCoefficientNumerics)
    (H : ℝ≥0), 1 ≤ H →
    ∃ CT CV : ℝ≥0, 0 < CT ∧ 0 < CV ∧
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
        (∀ Y : RawVector M, C.VectorHolder 2 metricBounds.exponent.value Y →
          projectedVectorOperator rho ghat z Y - projectedVectorOperator rho z z Y =
            covectorPiPerp rho (bianchi ghat (killing z Y) - bianchi z (killing z Y))) ∧
        (∀ Y : RawVector M, C.VectorHolder 2 metricBounds.exponent.value Y →
          projectedVectorOperator rho ghat g Y - projectedVectorOperator rho z z Y =
            projectedActualVectorDefect rho ghat z g Y) := by sorry
end K24.Global
