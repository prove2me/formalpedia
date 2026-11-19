-- Prove2me | Theorems.Thm_Kyprianou_Ch01_cosineEndpointDivTendstoZero
-- name    : Kyprianou.Ch01.cosineEndpointDivTendstoZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:07:21.897773+00:00
-- url     : https://prove2.me/theorems/23860fbd-cb44-47ad-ba21-5b4847a5a16f
-- title:
--   Vanishing cosine endpoint correction at infinity
-- statement:
--   The endpoint correction from integration by parts vanishes at infinity because the numerator 1 - cos R is bounded and the real denominator diverges.
-- source:
--   Kyprianou (2006), Chapter 1 stable α=1 integral and Dirichlet sine integral cutoff; sourced from exact positive-lower-cutoff integration by parts and cosine kernel integral, both already Proved.

import Mathlib
open MeasureTheory Filter Set Real
open scoped Topology Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.cosineEndpointDivTendstoZero :
    Tendsto (fun R : ℝ => (1 - Real.cos R) / R) atTop (𝓝 0) := by
  sorry
