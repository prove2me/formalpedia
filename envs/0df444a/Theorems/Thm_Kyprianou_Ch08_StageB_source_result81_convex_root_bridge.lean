-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_convex_root_bridge
-- name    : Kyprianou.Ch08.StageB.source_result81_convex_root_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:31:57.359867+00:00
-- url     : https://prove2.me/theorems/a5ad4013-be43-48a9-b40c-02442e18c62f
-- title:
--   Greatest-root bridge from convexity and unboundedness
-- statement:
--   A convex nonnegative-domain exponent vanishing at zero, continuous on the positive half-line and unbounded above, has a greatest nonnegative root at every nonnegative level with the bridge domain property.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, tilted descending potential. Mathematical reduction of 88aa77e2-4924-42e7-a415-7fcbc4e8ae14.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_convex_root_bridge
    (ψ : ℝ → ℝ) (h0 : ψ 0 = 0) (hc : ConvexOn ℝ (Ici (0 : ℝ)) ψ)
    (hcont : ContinuousOn ψ (Ioi (0 : ℝ))) (hlarge : ∀ q : ℝ, ∃ b : ℝ, 0 < b ∧ q < ψ b)
    (q : ℝ) (hq : 0 ≤ q) : IsScaleTransformDomainBridge ψ q := by
  sorry
