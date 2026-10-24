-- Prove2me | Theorems.Thm_K24_Global_cov2Holder_haarIntegrable
-- name    : K24.Global.cov2Holder_haarIntegrable
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T19:42:42.443033+00:00
-- url     : https://prove2.me/theorems/296e7358-6efb-4dba-9c4a-78ffe9b9cd6b
-- title:
--   K24 actual Holder tensors are fiberwise Haar integrable, including order zero
-- statement:
--   On any smooth manifold with the original four-dimensional charted space and a BoundedLocalCover C, every actual covariant two-tensor satisfying C.Cov2Holder k alpha is fiberwise Haar integrable under every original smooth CircleAction, for every natural k including zero and every nonnegative Holder exponent alpha. Compactness of the manifold, symmetry, and an action norm bound are unnecessary. This supplies the exact integrability condition for every member of the original tensorHolderSpace in the uniform conclusions.
-- source:
--   Original full K24 target aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22, uniform analytic residual 1a26d607-9f1f-4243-8fa0-c492842847f4; original unchanged Holder, canonical chart, action pullback and Haar definitions.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open scoped Manifold ContDiff NNReal ENNReal

namespace K24.Global
universe u
theorem cov2Holder_haarIntegrable :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (rho : CircleAction M)
      (k : ℕ) (alpha : ℝ≥0) (v : RawCov2 M),
      C.Cov2Holder k alpha v → Cov2HaarIntegrable rho v := by
  sorry
end K24.Global
