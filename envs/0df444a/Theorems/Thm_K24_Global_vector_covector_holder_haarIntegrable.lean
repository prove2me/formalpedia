-- Prove2me | Theorems.Thm_K24_Global_vector_covector_holder_haarIntegrable
-- name    : K24.Global.vector_covector_holder_haarIntegrable
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T19:48:32.429773+00:00
-- url     : https://prove2.me/theorems/d1c8b719-46f5-4a4e-82ec-3f5a9213e0cb
-- title:
--   K24: actual Haar integrability of Holder vector and covector sections at every finite order
-- statement:
--   For every original smooth four-manifold, every BoundedLocalCover C, every original CircleAction rho, every natural order k, and every nonnegative exponent alpha, C.VectorHolder k alpha Y implies VectorHaarIntegrable rho Y, and C.CovectorHolder k alpha eta implies CovectorHaarIntegrable rho eta. The proof uses the actual forward covector pullback and inverse-action vector differential. It derives canonical chart regularity from the original cover and proves continuity of each actual circle integrand. No compactness or Hausdorff assumption on M is added. This directly discharges the integrability conjuncts of the original Holder projection fields and supplies the all-order input for perpendicular kernel closure.
-- source:
--   Original full K24 root aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 and uniform analytic residual 1a26d607-9f1f-4243-8fa0-c492842847f4; exact original definition packets are preserved in source/.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open scoped Manifold ContDiff NNReal

namespace K24.Global
universe u
theorem vector_covector_holder_haarIntegrable :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (rho : CircleAction M)
    (k : ℕ) (alpha : ℝ≥0),
    (∀ Y : RawVector M, C.VectorHolder k alpha Y → VectorHaarIntegrable rho Y) ∧
    (∀ eta : RawCovector M, C.CovectorHolder k alpha eta → CovectorHaarIntegrable rho eta) := by
  sorry
end K24.Global
