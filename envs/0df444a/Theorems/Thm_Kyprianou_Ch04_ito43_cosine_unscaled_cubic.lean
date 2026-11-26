-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cosine_unscaled_cubic
-- name    : Kyprianou.Ch04.ito43_cosine_unscaled_cubic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:24:47.566585+00:00
-- url     : https://prove2.me/theorems/6cbdbf01-18bf-523f-beb0-8b4dab908dc1
-- title:
--   Unscaled cosine Taylor remainder has a cubic bound
-- statement:
--   The second derivative differs from minus one by at most the distance to zero. Apply the proved Taylor modulus to the segment from zero to the increment.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cosine_unscaled_cubic (x : ℝ) :
    |Real.cos x-1+x^2/2| ≤ |x| * x^2/2 := by sorry
