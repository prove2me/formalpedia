-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstStrictUpperCrossingBelowAnyLaterTimePublic
-- name    : Kyprianou.Ch01.firstStrictUpperCrossingBelowAnyLaterTimePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T10:22:25.254947+00:00
-- url     : https://prove2.me/theorems/1dc81851-c423-45d3-9589-a965d46a12aa
-- title:
--   Any time above first strict upper passage has an earlier strict crossing
-- statement:
--   For any real path with at least one strict upper crossing, every time strictly larger than the infimum of positive strict-crossing times has some positive strict-crossing time beneath it. This conditional completeness property is the order-theoretic ingredient for refining physical grids towards a continuous first-passage time.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.10(ii), grid-to-continuous passage approximation, back-of-book proof.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Defs
open Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstStrictUpperCrossingBelowAnyLaterTimePublic
    (f : ℝ≥0 → ℝ) (x : ℝ)
    (hcross : ∃ u : ℝ≥0, 0 < u ∧ x < f u)
    (t : ℝ≥0)
    (ht : sInf {u : ℝ≥0 | 0 < u ∧ x < f u} < t) :
    ∃ u : ℝ≥0, 0 < u ∧ x < f u ∧ u < t := by sorry
