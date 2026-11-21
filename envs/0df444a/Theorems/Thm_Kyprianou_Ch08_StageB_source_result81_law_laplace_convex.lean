-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_laplace_convex
-- name    : Kyprianou.Ch08.StageB.source_result81_law_laplace_convex
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T13:50:42.393005+00:00
-- url     : https://prove2.me/theorems/234005ff-f11f-4c9d-a493-5a38cf34d951
-- title:
--   Convexity of the actual nonnegative Laplace exponent
-- statement:
--   Apply Hölder at time one to the two exponential moments and use positivity to take logs.
-- source:
--   Kyprianou (2006), Chapter 8, transition from (8.6) to (8.7), pp. 214–215. Reduction of 052ed58f-ea64-42aa-b77f-405b74854fe2.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_law_laplace_convex
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) : ConvexOn ℝ (Ici 0) ψ := by
  sorry
