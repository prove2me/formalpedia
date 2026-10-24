-- Prove2me | Theorems.Thm_K24_Global_nativeLieTensorRegularity
-- name    : K24.Global.nativeLieTensorRegularity
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T19:03:33.916463+00:00
-- url     : https://prove2.me/theorems/1aa677cc-9445-4527-b644-9408128431ef
-- title:
--   K24: global C²-to-C¹ regularity of the actual Lie tensor
-- statement:
--   On every smooth real four-manifold modeled on the canonical four-dimensional Euclidean space, let g be an actual covariant two-tensor field and Y an actual vector field. If their canonical chart coefficients are C², then the actual Lie tensor lieTensor Y g has C¹ coefficients on every canonical chart target. No positivity, symmetry, metric condition, or compactness assumption is required. The conclusion includes genuine chart compatibility and gluing for the native point-dependent tensor reconstruction; compatibility of the Lie expression is proved, not assumed.
--
--   This supplies the output regularity needed to apply the K24 vector two-error identity from native C² inputs. Descent from bounded-cover Hölder regularity to native chart regularity, uniform Hölder and Sobolev estimates, and the remaining full K24 conclusions are separate obligations. The original FullK24Statement remains open.
--
--   Supporting the original full target https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §5 vector-operator formula (5.4), genuine Lie tensor regularity.

import Definitions.Def_K24GlobalGeometry

open K24.Global
open scoped Manifold ContDiff
universe u

theorem K24.Global.nativeLieTensorRegularity :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M],
    ∀ (g : RawCov2 M) (Y : RawVector M),
      Cov2ContDiff 2 g → VectorContDiff 2 Y → Cov2ContDiff 1 (lieTensor Y g) := by sorry
