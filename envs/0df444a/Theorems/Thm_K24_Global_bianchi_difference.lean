-- Prove2me | Theorems.Thm_K24_Global_bianchi_difference
-- name    : K24.Global.bianchi_difference
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T18:58:53.872624+00:00
-- url     : https://prove2.me/theorems/f873b555-6b29-4570-a524-66413c4e027d
-- title:
--   K24 exact Bianchi difference for C1 metric and tensor sections
-- statement:
--   On any smooth real four-manifold, let ghat and z be positive symmetric metric tensors, and let u be any covariant two-tensor. Assume all three tensor coefficient functions are C1 on every canonical chart target. At every point of every chart target, the difference of the two Bianchi operators on u equals the complete frozen bianchiDifferenceExpansion, including the derivative of the inverse-metric difference. This is the literal coordinate identity in ExactChangeOfSliceConclusions.bianchi_formula under explicit canonical C1 regularity. Deriving that regularity from the original lifted-cover Holder assumptions remains an open bridge; this child does not prove FullK24Statement.
-- source:
--   Original target aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22, ExactChangeOfSliceConclusions.bianchi_formula, frozen Def_K24GlobalGeometry bianchiInChart and bianchiDifferenceExpansion. Source K24 formula (3.4).

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open scoped Manifold ContDiff

namespace K24.Global
universe u
theorem bianchi_difference :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M],
      ∀ (ghat z u : RawCov2 M), IsMetric ghat → IsMetric z →
        Cov2ContDiff 1 ghat → Cov2ContDiff 1 z → Cov2ContDiff 1 u →
        ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
          ∀ j : Fin 4, bianchiInChart ghat u c x j - bianchiInChart z u c x j =
            bianchiDifferenceExpansion ghat z u c x j := by
  sorry
end K24.Global
