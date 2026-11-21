-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_compensated_real_integrable
-- name    : Kyprianou.Ch08.StageB.source_result81_compensated_real_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:23:26.383942+00:00
-- url     : https://prove2.me/theorems/9dbbb8c5-7f65-479c-b93e-5247aa69963b
-- title:
--   Integrability of the compensated real exponent on negative jumps
-- statement:
--   The compensated positive exponential is integrable against a Lévy measure carried by strictly negative jumps.
-- source:
--   Finite Lévy–Khintchine cutoff argument for Kyprianou (2006), Chapter 8, Theorem 8.1. Parent Prove2Me theorem 987aeaac-dbe6-4ff6-aca6-d87cd87bffde.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_compensated_real_integrable
    (ν : Measure ℝ) (hν : IsLevyMeasure ν) (hneg : ν (Ici (0 : ℝ)) = 0)
    (β : ℝ) (hβ : 0 ≤ β) :
    Integrable (fun y => Real.exp (β * y) - 1 - (if -1 < y then β * y else 0)) ν := by
  sorry
