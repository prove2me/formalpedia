-- Prove2me | Theorems.Thm_K24_Global_nativeWeitzenbockIdentity
-- name    : K24.Global.nativeWeitzenbockIdentity
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T20:20:31.479094+00:00
-- url     : https://prove2.me/theorems/1d59175f-041f-4cea-8818-4ab71902318e
-- title:
--   K24: native Bianchi-Killing Weitzenbock identity with canonical signs
-- statement:
--   For every smooth real four-manifold, every positive definite symmetric metric g with native C2 coefficients, and every vector field Y with native C2 coefficients, the actual canonical operators satisfy bianchi g (killing g Y) = roughVectorLaplacianFlat g Y - ricciVectorFlat g Y. Killing is the full Lie derivative, the rough Laplacian is the negative connection trace, and Ricci acts in the exact canonical slot convention. No compactness, Einstein, invariance, flatness or stronger smoothness hypothesis is added. The proof establishes genuine neighborhood Lie coefficient compatibility, metric compatibility, the inverse-metric derivative, the actual second-covariant-derivative curvature commutator and Ricci symmetry. It then recovers the original global sections at each point. This is the unprojected identity supporting the original exact change-of-slice conclusions; Holder-to-native regularity and Haar projection give its intended application. It does not prove the remaining uniform analytic estimates or full K24 mission. Parent https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §5, unnumbered displayed identity at pinned source lines 262–264, underlying unprojected Weitzenbock identity; exact signs and operators are the unchanged canonical K24GlobalGeometry definitions.

import Definitions.Def_K24GlobalGeometry

open scoped Manifold ContDiff
open K24.Global
universe u

set_option autoImplicit false

theorem K24.Global.nativeWeitzenbockIdentity :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] (g : RawCov2 M) (Y : RawVector M),
      IsMetric g → Cov2ContDiff 2 g → VectorContDiff 2 Y →
      bianchi g (killing g Y) = roughVectorLaplacianFlat g Y - ricciVectorFlat g Y := by sorry
