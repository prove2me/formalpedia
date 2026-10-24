-- Prove2me | Theorems.Thm_K24_Global_tensorSobolev_banach
-- name    : K24.Global.tensorSobolev_banach
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T20:49:17.928991+00:00
-- url     : https://prove2.me/theorems/fe471951-37f8-4c13-a881-01f38433c2c6
-- title:
--   Completeness of the original real-order tensor Sobolev section spaces
-- statement:
--   For every original smooth compact Hausdorff four-manifold, every actual BoundedLocalCover and SobolevPartition, every natural k and every real r>k+2, the original symmetric tensorSobolevSpace P k r is a SectionBanachSpace for exactly P.cov2SobolevENorm r. This proves all algebraic norm laws, pointwise definiteness and completeness on the original raw Ck tensor carrier. The original local Bessel norm and all unit cover/component square-sum weights are retained, with no covering-degree bound or normalization.
-- source:
--   Exact Definitions.Def_K24GlobalStatement tensorSobolevSpace and SobolevConclusions.domain_banach / target_banach under UniformSobolevStatement. The checked full-prefix original-field binding specializes k=2,r=s and k=0,r=s-2 for the original real s>4. Original source commit 8c02be189f097080feca952347c9104bfb986242.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
set_option maxSynthPendingDepth 16
open scoped NNReal ENNReal ContDiff

namespace K24.Global
universe u
theorem tensorSobolev_banach :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [CompactSpace M] [T2Space M],
    ∀ (C : BoundedLocalCover M) (P : SobolevPartition C) (k : ℕ) (r : ℝ),
      (k : ℝ) + 2 < r →
      SectionBanachSpace (tensorSobolevSpace P k r) (P.cov2SobolevENorm r) := by
  sorry
end K24.Global
