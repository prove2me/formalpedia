-- Prove2me | Theorems.Thm_K24_Global_affine_metric_einstein_residual_differentiable
-- name    : K24.Global.affine_metric_einstein_residual_differentiable
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-26T04:46:32.328636+00:00
-- url     : https://prove2.me/theorems/ddf68678-d3b4-48ab-bdb4-19c3450fa073
-- title:
--   K24: actual affine Einstein residual coefficient differentiability under C2 assumptions
-- statement:
--   For every smooth four-manifold, every actual metric z and arbitrary covariant two-tensor u whose canonical coefficients are C2, each literal Einstein residual coefficient of z+t u in any canonical chart target is differentiable at t=0. No symmetry of u, C3 spatial regularity, common global positivity interval, or operator differentiability assumption is added.
-- source:
--   Original root aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 and analytic core 3db797ab-2b53-4cda-b318-e4780235e38c; concrete coefficient differentiation prerequisite for original K24 product rule (2.1) and fixed linearization, using unchanged actual Einstein residual definitions.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open scoped Manifold ContDiff

namespace K24.Global
universe u

theorem affine_metric_einstein_residual_differentiable :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M],
    ∀ (z u : RawCov2 M), IsMetric z → Cov2ContDiff 2 z → Cov2ContDiff 2 u →
      ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
        ∀ (lam : ℝ) (i j : Fin 4),
          DifferentiableAt ℝ
            (fun t : ℝ => einsteinResidualInChart lam (z + t • u) c x i j) 0 := by sorry

end K24.Global
