-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49CountLinearBoundV4
-- name    : Kyprianou.Ch04.exercise49CountLinearBoundV4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:01:49.525479+00:00
-- url     : https://prove2.me/theorems/95048064-67f4-58c9-8b6e-49f6eacaba85
-- title:
--   exercise49CountLinearBoundV4
-- statement:
--   exercise49CountLinearBoundV4
-- source:
--   Exercise 4.9(iii) admissible model construction

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
variable {Ω : Type} [MeasurableSpace Ω]

theorem Kyprianou.Ch04.exercise49CountLinearBoundV4 (a : ℕ → ℝ) (K : ℝ → ℕ) (c : ℝ) (hc : 0 < c) (N : ℕ)
    (ha : ∀ n ≥ N, c * (n : ℝ) ≤ ∑ i ∈ Finset.range n, a i)
    (hK : ∀ t n, n < K t ↔ (∑ i ∈ Finset.range (n+1), a i) ≤ t) :
    ∀ t ≥ 0, (K t : ℝ) ≤ N + t / c := by sorry
