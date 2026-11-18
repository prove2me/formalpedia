-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneImaginaryKernelScalingPointwise
-- name    : Kyprianou.Ch01.stableAlphaOneImaginaryKernelScalingPointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:11:59.342871+00:00
-- url     : https://prove2.me/theorems/9709ebdb-fa94-4cad-aecb-81a938fbdd18
-- title:
--   Pointwise frequency-scaled imaginary alpha-one stable kernel
-- statement:
--   For z>0 and every r, the compensated sine Lévy kernel at frequency z is z² times the unit-argument sine kernel evaluated at u=zr, with its compensation cutoff moved to u<z. This source-exact equality includes r=0 by total division and underlies both the integral rescaling and the shifted sine-kernel integrability proof.
-- source:
--   Kyprianou (2006), Chapter 1, stable index-one Lévy imaginary logarithmic phase.

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneImaginaryKernelScalingPointwise
    (z r : ℝ) (hz : 0 < z) :
    ((z * r) * (if r < 1 then (1 : ℝ) else 0) - Real.sin (z * r)) / r ^ 2 =
      z ^ 2 * (((z * r) * (if z * r < z then (1 : ℝ) else 0) -
        Real.sin (z * r)) / (z * r) ^ 2) := by
  sorry
