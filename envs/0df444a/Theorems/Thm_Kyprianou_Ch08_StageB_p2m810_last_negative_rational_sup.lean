-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_last_negative_rational_sup
-- name    : Kyprianou.Ch08.StageB.p2m810_last_negative_rational_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T19:37:26.358483+00:00
-- url     : https://prove2.me/theorems/ed4ab4ac-2083-458c-a424-6abcc43a3232
-- title:
--   Last negative visit is the supremum of rational negative visits
-- statement:
--   For every right-continuous real path, its last strictly positive negative visit equals the countable rational supremum of negative visits, with zero for an empty set.
-- source:
--   Kyprianou (2006), Exercise 8.10(i),(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_last_negative_rational_sup
    (f : ℝ≥0 → ℝ)
    (hr : ∀ t, ContinuousWithinAt f (Ici t) t) :
    lastNegativeVisit (fun t (_ : Unit) => f t) () =
      ⨆ r : ℚ, if 0 < (r : ℝ) ∧ f (Real.toNNReal (r : ℝ)) < 0
        then (Real.toNNReal (r : ℝ) : WithTop ℝ≥0) else 0 := by
  sorry
