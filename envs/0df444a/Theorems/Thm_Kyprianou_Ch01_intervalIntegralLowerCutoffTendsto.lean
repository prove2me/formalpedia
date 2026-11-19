-- Prove2me | Theorems.Thm_Kyprianou_Ch01_intervalIntegralLowerCutoffTendsto
-- name    : Kyprianou.Ch01.intervalIntegralLowerCutoffTendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:21:40.428205+00:00
-- url     : https://prove2.me/theorems/5446c774-0e29-4915-a707-3b516a1b0426
-- title:
--   Lower endpoint convergence for an interval-integrable real kernel
-- statement:
--   For an arbitrary real interval-integrable kernel on [0,R], its integral over [a,R] converges to the integral over [0,R] as a approaches zero from above. This is a standard absolute-continuity consequence of interval integrability, and does not assume any sine or cosine source results.
-- source:
--   Pinned Mathlib intervalIntegral.continuousWithinAt_primitive, Kyprianou Chapter 1 Dirichlet sine integral finite cutoff.

import Mathlib
open MeasureTheory Filter Set Real
open scoped Topology Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.intervalIntegralLowerCutoffTendsto (f : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hint : IntervalIntegrable f volume 0 R) :
    Tendsto (fun a : ℝ => ∫ x in a..R, f x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in (0 : ℝ)..R, f x)) := by
  sorry
