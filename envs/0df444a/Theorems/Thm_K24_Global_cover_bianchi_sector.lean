-- Prove2me | Theorems.Thm_K24_Global_cover_bianchi_sector
-- name    : K24.Global.cover_bianchi_sector
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-26T04:57:05.214365+00:00
-- url     : https://prove2.me/theorems/41ae6e8a-1a18-4942-a8c9-f56de71ba604
-- title:
--   K24 Bianchi preserves the original zero-mean tensor sector
-- statement:
--   Under the unchanged original uniform natural Holder geometric assumptions, every original tensorHolderPerp order-two input u has actual zero Haar mean after applying either Bianchi ghat or Bianchi z. IsNonzeroCovector means Haar mean equals zero and includes zero. Arbitrary-input Bianchi action equivariance and justified dominated coordinate differentiation under Haar integration are derived from the original assumptions. No additional regularity, integrability, covariance, or commutation hypothesis is added. The unused CT/CV/lam binders are retained from the original prefix; no norm estimate or full analytic core conclusion is asserted.
-- source:
--   Original full root aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22; analytic core 3db797ab-2b53-4cda-b318-e4780235e38c; literal ExactChangeOfSliceConclusions.bianchi_sector under unchanged UniformHolderNaturalStatement prefix.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open scoped NNReal ENNReal Manifold ContDiff

namespace K24.Global
universe u
theorem cover_bianchi_sector :
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
        ∀ u ∈ tensorHolderPerp C 2 metricBounds.exponent.value rho,
          IsNonzeroCovector rho (bianchi ghat u) ∧ IsNonzeroCovector rho (bianchi z u) := by sorry
end K24.Global
