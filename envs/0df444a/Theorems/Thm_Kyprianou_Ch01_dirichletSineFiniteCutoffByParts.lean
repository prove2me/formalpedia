-- Prove2me | Theorems.Thm_Kyprianou_Ch01_dirichletSineFiniteCutoffByParts
-- name    : Kyprianou.Ch01.dirichletSineFiniteCutoffByParts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:02:45.764029+00:00
-- url     : https://prove2.me/theorems/9be49983-7d45-476f-9c1b-53edaa656bc5
-- title:
--   Positive-horizon Dirichlet sine integral equals cosine-kernel integral plus endpoint correction
-- statement:
--   Exact finite-upper-cutoff integration by parts for the Dirichlet sine integral, with the removable zero endpoint handled. Its positive-lower-end precursor stableAlphaOneCosineFiniteIntegrationByParts is already Proved.
-- source:
--   Kyprianou (2006), Chapter 1 stable α=1 integral and Dirichlet sine integral cutoff; sourced from exact positive-lower-cutoff integration by parts and cosine kernel integral, both already Proved.

import Mathlib
open MeasureTheory Filter Set Real
open scoped Topology Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.dirichletSineFiniteCutoffByParts
    (R : ℝ) (hR : 0 < R) :
    (∫ x in (0 : ℝ)..R, Real.sin x / x) =
      (∫ x in Set.Ioc (0 : ℝ) R, (1 - Real.cos x) / x ^ 2 ∂volume) +
      (1 - Real.cos R) / R := by
  sorry
