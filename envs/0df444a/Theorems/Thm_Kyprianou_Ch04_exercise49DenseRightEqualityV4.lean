-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49DenseRightEqualityV4
-- name    : Kyprianou.Ch04.exercise49DenseRightEqualityV4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:01:50.034746+00:00
-- url     : https://prove2.me/theorems/2d8b192c-05ec-480e-a7f1-df2c8dfc1187
-- title:
--   exercise49DenseRightEqualityV4
-- statement:
--   exercise49DenseRightEqualityV4
-- source:
--   Exercise 4.9(iii) admissible model construction

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
variable {Ω : Type} [MeasurableSpace Ω]

theorem Kyprianou.Ch04.exercise49DenseRightEqualityV4 (x y : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (hx : ∀ s, ContinuousWithinAt x (Ici s) s)
    (hy : ∀ s, ContinuousWithinAt y (Ici s) s)
    (he : ∀ k, x (q k) = y (q k)) : x = y := by sorry
