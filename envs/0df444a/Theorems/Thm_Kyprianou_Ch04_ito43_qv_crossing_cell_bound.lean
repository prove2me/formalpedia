-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_qv_crossing_cell_bound
-- name    : Kyprianou.Ch04.ito43_qv_crossing_cell_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:42:13.98692+00:00
-- url     : https://prove2.me/theorems/449fc62e-0b47-4c99-9a96-cb43cc388766
-- title:
--   Quadratic energy error on a split grid cell
-- statement:
--   Expand the square and apply the triangle inequality to bound the cross term by a uniform bound on the first increment and the vanishing second increment.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_qv_crossing_cell_bound (A B M : ℝ) (hA : |A| ≤ M) :
    |(A+B)^2-A^2| ≤ 2*M*|B|+B^2 := by sorry
