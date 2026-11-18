-- Prove2me | Theorems.Thm_Kyprianou_Ch01_dirichletSineIntegralCutoff
-- name    : Kyprianou.Ch01.dirichletSineIntegralCutoff
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T09:10:42.205613+00:00
-- url     : https://prove2.me/theorems/338992ff-d9b0-4b22-9a66-261266088205
-- title:
--   Dirichlet sine integral π/2 as the real improper cutoff limit
-- statement:
--   As the upper integration bound R tends to positive infinity, the ordinary real integral from 0 to R of sin(x)/x tends to π/2. This is the Dirichlet sine integral in its conditionally convergent cutoff form, rather than the Lebesgue integral over the entire positive half-line. It supplies the numerical analytic input for the index-one stable cosine integral, whose absolute integrability and integration-by-parts endpoints have been established independently.
-- source:
--   Kyprianou (2006), Chapter 1, stable index-one Lévy exponent; classical Dirichlet sine integral after finite-interval integration by parts.

import Mathlib
open MeasureTheory Filter Set Real
open scoped Topology Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.dirichletSineIntegralCutoff :
    Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sin x / x)
    atTop (𝓝 (Real.pi / 2)) := by
  sorry
