-- Prove2me | Theorems.Thm_K24_Global_tensorDefectPrincipalSymbolNative
-- name    : K24.Global.tensorDefectPrincipalSymbolNative
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T19:56:10.805169+00:00
-- url     : https://prove2.me/theorems/cff62489-d206-4a3e-a3a9-ba71a3436b8a
-- title:
--   K24: the actual tensor defect principal symbol on every smooth four-manifold
-- statement:
--   For every smooth real four-manifold, every pair of symmetric positive definite native C2 metrics ghat and z, every valid canonical chart point x, every real covector xi, every arbitrary real 4 by 4 matrix A and all two output indices, the actual tensorDefectPrincipalSymbol equals the canonical tensorDefectSymbolFormula. No symmetry assumption is imposed on A.
--
--   The left side uses the actual globally reconstructed quadratic test tensor, actual Bianchi difference and actual deltaStar, followed by chart coefficient extraction. The conclusion is proved by genuine local differentiability, chart transformations, local reconstruction and actual second derivatives of that quadratic tensor; global differentiability of the chart-defined test tensor outside its chart is not assumed. No coordinate compatibility or symbol formula is supplied as a premise.
--
--   This is the original principal-symbol identity at explicit native C2 metric regularity. The bounded-cover-to-native regularity bridge, quantitative symbol bound and the other uniform analytic conclusions are separate obligations. The result does not close the original FullK24Statement. Parent https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 ; current analytic frontier https://prove2.me/theorems/3db797ab-2b53-4cda-b318-e4780235e38c .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §3, equations (3.6)–(3.7), with the unchanged canonical geometric definitions.

import Definitions.Def_K24GlobalGeometry
set_option autoImplicit false
open scoped Manifold ContDiff Matrix.Norms.Elementwise
open K24.Global
universe u

theorem K24.Global.tensorDefectPrincipalSymbolNative :
∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] (ghat z : RawCov2 M),
      IsMetric ghat → IsMetric z → Cov2ContDiff 2 ghat → Cov2ContDiff 2 z →
      ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
      ∀ (xi : Fin 4 → ℝ) (A : Mat4) (i j : Fin 4),
        tensorDefectPrincipalSymbol ghat z c x xi A i j =
          tensorDefectSymbolFormula ghat z c x xi A i j := by sorry
