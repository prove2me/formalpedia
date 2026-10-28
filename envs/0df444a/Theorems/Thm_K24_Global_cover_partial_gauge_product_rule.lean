-- Prove2me | Theorems.Thm_K24_Global_cover_partial_gauge_product_rule
-- name    : K24.Global.cover_partial_gauge_product_rule
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-26T05:12:33.777164+00:00
-- url     : https://prove2.me/theorems/2585878e-3357-4dc1-9488-8acd6b22e129
-- title:
--   K24: exact partial-gauge product rule under the original natural hypotheses
-- statement:
--   Under the complete original natural Holder prefix, for every variation u in the original tensorHolderSpace of order two, the actual coefficient derivative partialGaugeVariation equals partialGaugeProductRule, including its metric-variation term and the genuine projected Bianchi term. No C3 metric assumption, supplied differentiability, Haar mean C1, or global positive affine interval is added.
-- source:
--   Original K24 root aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22; analytic core 3db797ab-2b53-4cda-b318-e4780235e38c; literal ExactChangeOfSliceConclusions.product_rule, source equation (2.1). Original3 definitions and root/core packets preserved under research-context/.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open scoped Manifold ContDiff NNReal

namespace K24.Global
universe u

theorem cover_partial_gauge_product_rule :
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
        ∀ u ∈ tensorHolderSpace C 2 metricBounds.exponent.value,
          partialGaugeVariation rho lam ghat z u = partialGaugeProductRule rho lam ghat z u := by sorry

end K24.Global
