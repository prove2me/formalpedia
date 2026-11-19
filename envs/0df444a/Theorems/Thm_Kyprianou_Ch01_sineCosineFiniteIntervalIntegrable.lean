-- Prove2me | Theorems.Thm_Kyprianou_Ch01_sineCosineFiniteIntervalIntegrable
-- name    : Kyprianou.Ch01.sineCosineFiniteIntervalIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:23:16.99859+00:00
-- url     : https://prove2.me/theorems/7bf99a9b-d508-447d-9307-8d0490fc53b0
-- title:
--   Finite-interval absolute integrability of sine quotient and cosine kernel
-- statement:
--   Both sin(x)/x and (1-cos(x))/x² are interval-integrable over [0,R] for any R>0. The sine quotient differs only at x=0 from the continuous sinc function, while cosine-kernel integrability on the whole positive line is already-Proved by Kyprianou.Ch01.stableAlphaOneCosineIntegral.
-- source:
--   Kyprianou Chapter 1 stable index-one integral and Dirichlet cutoff, using Mathlib Real.continuous_sinc and Proved stableAlphaOneCosineIntegral.

import Mathlib
open MeasureTheory Filter Set Real
open scoped Topology Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.sineCosineFiniteIntervalIntegrable
    (R : ℝ) (hR : 0 < R) :
    IntervalIntegrable (fun x : ℝ => Real.sin x / x) volume 0 R ∧
    IntervalIntegrable
      (fun x : ℝ => (1 - Real.cos x) / x ^ 2) volume 0 R := by
  sorry
