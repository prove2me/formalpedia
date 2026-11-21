-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_coefficient_when_positive_zero_root
-- name    : Kyprianou.Ch08.StageB.source_result81_coefficient_when_positive_zero_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T13:50:36.736467+00:00
-- url     : https://prove2.me/theorems/fb394d42-bf45-47e9-986d-0bd07a8435bd
-- title:
--   Discount coefficient when the largest zero root is positive
-- statement:
--   Monotonicity of convex secants keeps Phi(q) above the positive largest zero root. Squeeze q/Phi(q) to zero. The same secant monotonicity makes a positive finite right slope at zero impossible.
-- source:
--   Kyprianou (2006), Chapter 8, transition from (8.6) to (8.7), pp. 214–215. Reduction of 052ed58f-ea64-42aa-b77f-405b74854fe2.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_coefficient_when_positive_zero_root
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (hconv : ConvexOn ℝ (Ici 0) ψ) (hzero : ψ 0 = 0) (hφ0 : 0 < Phi ψ 0) :
    (∀ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d →
      Tendsto (fun q : ℝ => q / Phi ψ q)
        (nhdsWithin 0 (Ioi 0)) (nhds d)) ∧
    ((¬ ∃ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d) →
      Tendsto (fun q : ℝ => q / Phi ψ q)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)) := by
  sorry
