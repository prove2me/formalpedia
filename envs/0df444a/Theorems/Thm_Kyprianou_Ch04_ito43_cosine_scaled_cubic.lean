-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cosine_scaled_cubic
-- name    : Kyprianou.Ch04.ito43_cosine_scaled_cubic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:24:50.336111+00:00
-- url     : https://prove2.me/theorems/223bb460-926f-4fc4-a4fa-a9e55a46e31e
-- title:
--   Scaled cosine remainder is bounded by frequency times cubic mark
-- statement:
--   Multiply the scaled remainder by the positive frequency square and apply the unscaled cubic estimate, then cancel the positive factor.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cosine_scaled_cubic (a z : ℝ) (ha : 0 < a) :
    |z^2/2-(1-Real.cos (a*z))/a^2| ≤ a*|z| * z^2/2 := by sorry
