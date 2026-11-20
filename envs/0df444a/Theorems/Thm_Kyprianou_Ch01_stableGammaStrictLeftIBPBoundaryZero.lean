-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftIBPBoundaryZero
-- name    : Kyprianou.Ch01.stableGammaStrictLeftIBPBoundaryZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:19:41.905745+00:00
-- url     : https://prove2.me/theorems/b0d450f7-d87d-44fd-9b1b-071f3dba4322
-- title:
--   Both exact strict-left Gamma integration-by-parts boundary products vanish
-- statement:
--   The product (exp(wr)-1) r^(−alpha)/(−alpha) tends to zero both as r→0+ and as r→+∞, when 0<alpha<1 and Re(w)<0. Near zero the first-order complex exponential remainder gives r^(1-alpha); infinity uses bounded numerator and decaying inverse power.
-- source:
--   Kyprianou (2006), Chapter 1, complex stable Gamma deficit integral, source exact analytic half-line integration by parts.

import Mathlib
open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftIBPBoundaryZero
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re < 0) :
    Tendsto
      (fun r : ℝ => (Complex.exp (w * (r : ℂ)) - 1) * (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℂ)) ∧
    Tendsto
      (fun r : ℝ => (Complex.exp (w * (r : ℂ)) - 1) * (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ))
      Filter.atTop (nhds (0 : ℂ)) := by sorry
