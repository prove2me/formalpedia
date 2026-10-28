-- Prove2me | Theorems.Thm_K24_Global_deltaStar_chart_recovery_and_action_naturality_c1
-- name    : K24.Global.deltaStar_chart_recovery_and_action_naturality_c1
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-26T05:12:06.000353+00:00
-- url     : https://prove2.me/theorems/78671b07-078a-44cf-b8a9-5f85aa7801fa
-- title:
--   C1 chart recovery and arbitrary circle-action naturality of the actual symmetrized covector derivative
-- statement:
--   The statement assumes a smooth four-manifold, a positive definite symmetric metric g with canonical C1 coefficients, and a covector eta with canonical C1 coefficients. It proves both that the actual reconstructed deltaStar g eta has the stated deltaStarInChart coefficients in every valid chart and that simultaneous pullback of the metric and covector by an arbitrary smooth circle action commutes with deltaStar. There is no invariance or pointwise-vanishing premise, and no C2 hypothesis on g or eta.
-- source:
--   Actual deltaStar and deltaStarInChart definitions in unchanged K24GlobalGeometry; connected coordinate compatibility needed by original ExactChangeOfSliceConclusions equivariant_fixed, equivariant_reanchored and tensor_sector fields. Original root aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 and analytic core 3db797ab-2b53-4cda-b318-e4780235e38c.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open scoped Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global
universe u
theorem deltaStar_chart_recovery_and_action_naturality_c1 :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M],
    ∀ (g : RawCov2 M) (eta : RawCovector M),
      IsMetric g → Cov2ContDiff 1 g → CovectorContDiff 1 eta →
      (∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
        ∀ i j : Fin 4, cov2InChart (deltaStar g eta) c x i j = deltaStarInChart g eta c x i j) ∧
      (∀ (rho : CircleAction M) (t : Circle),
        deltaStar (actionPullbackCov2 rho t g) (actionPullbackCovector rho t eta) =
          actionPullbackCov2 rho t (deltaStar g eta)) := by sorry
end K24.Global
