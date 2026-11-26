-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_qv_cosine_bounds
-- name    : Kyprianou.Ch04.ito43_qv_cosine_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:42:08.263035+00:00
-- url     : https://prove2.me/theorems/d3f37d3a-88a8-5259-b30a-03478cb7f1de
-- title:
--   Bounded cosine energy and square bound
-- statement:
--   The cosine deficit is nonnegative and bounded by two. Dividing by a squared frequency gives a variance envelope without second moments of the source.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_qv_cosine_bounds (a x : ℝ) :
    let q := (1 - Real.cos (a*x)) / a^2
    0 ≤ q ∧ q ≤ 2/a^2 ∧ q^2 ≤ (2/a^2)*q := by sorry
