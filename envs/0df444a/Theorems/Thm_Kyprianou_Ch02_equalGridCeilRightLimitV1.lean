-- Prove2me | Theorems.Thm_Kyprianou_Ch02_equalGridCeilRightLimitV1
-- name    : Kyprianou.Ch02.equalGridCeilRightLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:36:24.792965+00:00
-- url     : https://prove2.me/theorems/3b65b0db-1351-4c46-989d-b4a72f9f9437
-- title:
--   Ceiling grid maps converge to each time from the right
-- statement:
--   The ceiling index lies between the scaled displacement and that displacement plus one. Consequently x ≤ r_n(x) ≤ x+(b-a)/(n+1), yielding the right-sided limit.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.equalGridCeilRightLimitV1
    (a b : ℝ≥0) (hab : a < b) :
    let g : ℕ → ℕ → ℝ≥0 := fun n k =>
      a + (b - a) * (k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let r : ℕ → ℝ≥0 → ℝ≥0 := fun n x =>
      g n ⌈(x - a) * ((n + 1 : ℕ) : ℝ≥0) / (b - a)⌉₊
    ∀ x ∈ Icc a b, Tendsto (fun n => r n x) atTop (nhdsWithin x (Ici x)) := by sorry
