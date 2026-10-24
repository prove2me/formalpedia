-- Prove2me | Theorems.Thm_K24_Global_cover_inner_bilinear_holder_bound
-- name    : K24.Global.cover_inner_bilinear_holder_bound
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T19:58:58.705775+00:00
-- url     : https://prove2.me/theorems/e6e2f63d-b587-4b13-aa90-59dbbb0b05f6
-- title:
--   All finite-order Hölder bilinear coefficient bounds from original outer to inner cover domains
-- statement:
--   For every finite order k, original HolderExponent alpha, and original cover numerics, there is a finite positive constant K depending only on those numerical data such that, for every actual local cover chart with those numerics and every continuous bilinear map B between real normed spaces, two functions satisfying the original BigHolderOn k alpha on its outer domain have a bilinear product satisfying the original BigHolderOn k alpha on its inner domain. Its original inner coordinateHolderENorm is bounded by K times the actual norm of B times the two original outer coordinateHolderENorm values. No convexity assumption is added. This is an inner/outer coefficient estimate, not a same-domain arbitrary-section algebra statement.
-- source:
--   Original Full K24 root aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22, uniform analytic residual 1a26d607-9f1f-4243-8fa0-c492842847f4. Uses unchanged coordinateHolderENorm, BigHolderOn, BoundedLocalCover.uniformShrink and uniformOuterRadius from Def_K24GlobalAnalysis, with a checked MetricAdmissible coefficient specialization.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open scoped NNReal ENNReal ContDiff

namespace K24.Global
universe u v w z

theorem cover_inner_bilinear_holder_bound :
  ∀ (k : ℕ) (alpha : HolderExponent) (coverBounds : CoverNumerics),
    ∃ K : ℝ≥0, 0 < K ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
        (C : BoundedLocalCover M), C.numerics = coverBounds →
      ∀ (ν : C.Index) (E : Type v) (F : Type w) (G : Type z)
        [NormedAddCommGroup E] [NormedSpace ℝ E]
        [NormedAddCommGroup F] [NormedSpace ℝ F]
        [NormedAddCommGroup G] [NormedSpace ℝ G]
        (B : E →L[ℝ] F →L[ℝ] G) (f : FourSpace → E) (g : FourSpace → F),
        BigHolderOn k alpha.value (C.chart ν).outerDomain f →
        BigHolderOn k alpha.value (C.chart ν).outerDomain g →
        BigHolderOn k alpha.value (C.chart ν).innerDomain (fun x => B (f x) (g x)) ∧
        coordinateHolderENorm k alpha.value (C.chart ν).innerDomain (fun x => B (f x) (g x)) ≤
          (K : ℝ≥0∞) * (‖B‖₊ : ℝ≥0∞) *
            coordinateHolderENorm k alpha.value (C.chart ν).outerDomain f *
            coordinateHolderENorm k alpha.value (C.chart ν).outerDomain g := by
  sorry

end K24.Global
