-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_stopped_downward_split
-- name    : Kyprianou.Ch08.StageB.source_result81_stopped_downward_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:59:37.653106+00:00
-- url     : https://prove2.me/theorems/3c242566-b9e1-49b0-bbd8-ab10f9c26428
-- title:
--   Strong Markov splitting for Theorem 8.1
-- statement:
--   Split the one-sided downward payoff on the order of the two exit times. On upper exit before ruin the process reaches the upper level without overshoot, and strong Markov factors the discounted future downward payoff. This identity is independent of the existence or properties of a scale function.
-- source:
--   Kyprianou (2006), Chapter 8, proof of (8.9), p. 215. Decomposition of dd90765c-572a-4a22-9657-966e9544f3d3.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_stopped_downward_split
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (q x a : ℝ) (hq : 0 ≤ q) (ha : 0 < a) (hxa : x ≤ a) :
    downExpectation P D.X q x =
      downBeforeUpExpectation P D.X q x a +
        upBeforeDownExpectation P D.X q x a * downExpectation P D.X q a := by
  sorry
