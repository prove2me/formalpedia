-- Prove2me | Theorems.Thm_K24_Global_nativeBianchiDeltaStarChartRecovery
-- name    : K24.Global.nativeBianchiDeltaStarChartRecovery
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T19:45:23.066496+00:00
-- url     : https://prove2.me/theorems/aa5cdc73-f41d-4989-afd3-5d7fc22929dd
-- title:
--   K24: native Bianchi and deltaStar recovery in every valid chart
-- statement:
--   On every smooth real four-manifold, every symmetric positive definite native C1 metric has the following coordinate recovery properties. For every native C1 covariant two-tensor (not required to be symmetric), coefficients of its actual Bianchi covector equal the canonical Bianchi chart formula in every valid canonical chart. For every native C1 covector, coefficients of its actual symmetric gradient deltaStar equal the canonical chart formula in every valid canonical chart. No coordinate compatibility or operator identification is assumed. The proof derives the Christoffel Hessian law and actual reconstruction. This is not a uniform norm estimate, a principal-symbol theorem for a merely chart-local quadratic test, or completion of FullK24Statement.
--
--   Supporting unchanged original full target https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §3, equations (3.2)–(3.3) and the canonical native operator definitions

import Definitions.Def_K24GlobalGeometry
set_option autoImplicit false
open scoped Manifold ContDiff Matrix.Norms.Elementwise
open K24.Global
universe u

theorem K24.Global.nativeBianchiDeltaStarChartRecovery :
∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] (g : RawCov2 M),
      IsMetric g → Cov2ContDiff 1 g →
        ((∀ u : RawCov2 M, Cov2ContDiff 1 u →
          ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
            covectorInChart (bianchi g u) c x = bianchiInChart g u c x) ∧
         (∀ eta : RawCovector M, CovectorContDiff 1 eta →
          ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
            cov2InChart (deltaStar g eta) c x = deltaStarInChart g eta c x)) := by sorry
