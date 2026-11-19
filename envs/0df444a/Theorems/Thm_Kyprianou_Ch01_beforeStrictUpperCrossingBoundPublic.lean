-- Prove2me | Theorems.Thm_Kyprianou_Ch01_beforeStrictUpperCrossingBoundPublic
-- name    : Kyprianou.Ch01.beforeStrictUpperCrossingBoundPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:31:45.325887+00:00
-- url     : https://prove2.me/theorems/33889a88-528b-45b5-a639-a9b5d096dec9
-- title:
--   Pathwise barrier bound strictly before the infimum of strict positive upper crossings
-- statement:
--   For any real path indexed by nonnegative times that starts at or below a barrier, at any time strictly less than the infimum of positive strict crossings, the path is at or below that barrier. No continuity or probability assumptions are required. This is the pre-crossing bound for the exponentially stopped Brownian martingale.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.10(ii), bounded stopped-exponential domination, printed page 306 (PDF 312).

import Mathlib.Data.NNReal.Defs
open Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.beforeStrictUpperCrossingBoundPublic (f : ℝ≥0 → ℝ) (x : ℝ)
    (hstart : f 0 ≤ x) (t : ℝ≥0)
    (ht : t < sInf {u : ℝ≥0 | 0 < u ∧ x < f u}) :
    f t ≤ x := by sorry
