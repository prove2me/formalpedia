-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_strict_lower_clock_shift
-- name    : Kyprianou.Ch08.StageB.source_result81_strict_lower_clock_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T13:23:07.969572+00:00
-- url     : https://prove2.me/theorems/f14da840-8d70-4bdc-a8ce-5c003f26e95a
-- title:
--   Translate a strict lower clock after a time preceding the crossing
-- statement:
--   Every lower crossing lies strictly after the prescribed time. Translate the crossing set by this time and commute finite addition with the extended-real infimum, including the empty crossing set.
-- source:
--   Kyprianou (2006), Chapter 8, proof of (8.9), p. 215. Pathwise reduction of b0b69794-330e-4301-89b9-d19ecb9fa31f.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open Set Filter Topology MeasureTheory ProbabilityTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_strict_lower_clock_shift
    (f : ℝ≥0 → ℝ) (t : ℝ≥0)
    (hbefore : (t : WithTop ℝ≥0) < tauMinus (fun s (_ : Unit) => f s) 0 ()) :
    tauMinus (fun s (_ : Unit) => f s) 0 () =
      (t : WithTop ℝ≥0) + tauMinus (fun s (_ : Unit) => f (t + s)) 0 () := by
  sorry
