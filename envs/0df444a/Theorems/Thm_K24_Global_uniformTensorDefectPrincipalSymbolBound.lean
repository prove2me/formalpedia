-- Prove2me | Theorems.Thm_K24_Global_uniformTensorDefectPrincipalSymbolBound
-- name    : K24.Global.uniformTensorDefectPrincipalSymbolBound
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T20:36:38.765132+00:00
-- url     : https://prove2.me/theorems/dca840ce-5e52-44e3-a4f2-ec273083a8e7
-- title:
--   K24: uniform weighted bound for the actual tensor-defect principal symbol
-- statement:
--   For every original MetricCoefficientNumerics b there exists a strictly positive finite constant CT, chosen before every manifold, cover and metric pair, with the following property. For every smooth real four-manifold, original bounded local cover, and two metrics ghat,z satisfying the unchanged MetricAdmissible C b hypotheses, the actual native principal symbol of tensorDefect is bounded at every valid native chart point by CT times the z-induced Hilbert–Schmidt norm of ghat-z, times the square of the z-induced covector norm of xi, times the z-induced Hilbert–Schmidt norm of A. The matrix A is arbitrary and need not be symmetric. The theorem uses the actual quadratic-jet symbol definition and the exact canonical square-root contraction norms, not a replacement symbol polynomial or a coordinate sup norm.
--
--   The proof first derives intrinsic relative metric comparability from the actual covering frames and original coefficient ellipticity bounds. It identifies the actual native symbol with its proved coefficient formula. An actual positive square-root frame reduces the weighted tensor norm to the full Frobenius norm; inverse-matrix differences, rank-one symmetrization and norm estimates give CT=12/(b.lower/b.upper). This value depends only on the original numerical metric data. No compactness, Hausdorffness, pointwise comparability premise, amplitude symmetry or extra regularity assumption is added. This closes the original quantitative symbol-estimate field. Global Holder/Sobolev operator estimates and the remaining K24 mission remain open.
--
--   Parent https://prove2.me/theorems/3db797ab-2b53-4cda-b318-e4780235e38c .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §3 principal-symbol formula and estimate, equations (3.6)–(3.7); exact symbol and weighted metric norms are the unchanged canonical K24 definitions.

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
open K24.Global
open scoped Manifold ContDiff NNReal ENNReal Matrix.Norms.Elementwise
universe u

theorem K24.Global.uniformTensorDefectPrincipalSymbolBound :
  ∀ b : MetricCoefficientNumerics, ∃ CT : ℝ≥0, 0 < CT ∧
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M],
    ∀ (C : BoundedLocalCover M) (ghat z : RawCov2 M),
      MetricAdmissible C b ghat → MetricAdmissible C b z →
      ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
      ∀ (xi : Fin 4 → ℝ) (A : Mat4),
        metricTensorPointNorm z c x (tensorDefectPrincipalSymbol ghat z c x xi A) ≤
          (CT : ℝ) * metricTensorPointNorm z c x (cov2InChart (ghat-z) c x) *
            (metricCovectorPointNorm z c x xi)^2 * metricTensorPointNorm z c x A := by sorry
