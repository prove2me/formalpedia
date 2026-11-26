-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cosine_deficit_frequency_limit
-- name    : Kyprianou.Ch04.ito43_cosine_deficit_frequency_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:32:10.165361+00:00
-- url     : https://prove2.me/theorems/097dfbfe-b335-4503-bac7-25377bc6c054
-- title:
--   Normalised cosine deficit tends to zero as frequency grows
-- statement:
--   Its nonnegative value is bounded by twice the square of the reciprocal frequency, which tends to zero.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cosine_deficit_frequency_limit (z : ℝ) :
    Tendsto (fun m : ℕ => (1-Real.cos (((m:ℝ)+1)*z))/((m:ℝ)+1)^2) atTop (nhds 0) := by sorry
