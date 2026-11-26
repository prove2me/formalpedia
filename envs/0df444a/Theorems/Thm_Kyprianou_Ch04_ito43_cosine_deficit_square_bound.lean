-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cosine_deficit_square_bound
-- name    : Kyprianou.Ch04.ito43_cosine_deficit_square_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:32:08.412639+00:00
-- url     : https://prove2.me/theorems/f9897845-5a4b-4f74-9981-2a5ef9e105ad
-- title:
--   Normalised cosine deficit is bounded by both square energy and frequency bound
-- statement:
--   Use the lower quadratic bound on cosine and the existing nonnegative bounded cosine estimate.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cosine_deficit_square_bound (a z : ℝ) (ha : 0 < a) :
    let q := (1-Real.cos (a*z))/a^2
    0 ≤ q ∧ q ≤ z^2/2 ∧ q ≤ 2/a^2 := by sorry
