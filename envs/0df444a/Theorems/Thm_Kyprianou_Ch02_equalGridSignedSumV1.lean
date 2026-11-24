-- Prove2me | Theorems.Thm_Kyprianou_Ch02_equalGridSignedSumV1
-- name    : Kyprianou.Ch02.equalGridSignedSumV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:50:18.358058+00:00
-- url     : https://prove2.me/theorems/a8515e44-8420-4c29-9466-4dc1af50ff58
-- title:
--   Equal-grid signed increments telescope
-- statement:
--   Use the finite range telescoping identity and the two endpoints.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.equalGridSignedSumV1
    (f : ℝ≥0 → ℝ) (a b : ℝ≥0) (hab : a ≤ b) (n : ℕ) :
    let g (k : ℕ) : ℝ≥0 := a+(b-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
    (∑ k : Fin (n+1), (f (g (k.val+1))-f (g k.val))) = f b-f a := by sorry
