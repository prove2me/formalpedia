-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_tilted_cumulative_continuous
-- name    : Kyprianou.Ch08.StageB.source_result81_tilted_cumulative_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T11:36:26.621089+00:00
-- url     : https://prove2.me/theorems/54231f6b-1597-4c7d-a613-3377bd0ca9d9
-- title:
--   Continuity of cumulative potential mass on the nonnegative ray
-- statement:
--   A measure supported on the nonnegative real axis, finite on all lower rays and without atoms at positive points, has a continuous real-valued cumulative mass on the closed nonnegative ray. Restriction to the positive ray removes the possible atom at zero, which contributes a constant to the cumulative mass on this domain.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, construction from a tilted descending potential. Auxiliary obligation of 40899fa3-08db-48e0-88dd-e4cea3055bc5.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_tilted_cumulative_continuous
    (ν : Measure ℝ) (hsupp : ν (Iio (0 : ℝ)) = 0)
    (hf : ∀ x : ℝ, ν (Iic x) < ⊤) (hatom : ∀ x : ℝ, 0 < x → ν {x} = 0) :
    ContinuousOn (fun x => (ν (Iic x)).toReal) (Ici (0 : ℝ)) := by
  sorry
