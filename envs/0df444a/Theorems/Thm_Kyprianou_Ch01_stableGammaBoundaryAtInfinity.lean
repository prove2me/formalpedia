-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaBoundaryAtInfinity
-- name    : Kyprianou.Ch01.stableGammaBoundaryAtInfinity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:36:50.706383+00:00
-- url     : https://prove2.me/theorems/da9e328b-e859-45f9-a11d-33aabb28aa4f
-- title:
--   Stable Gamma integration-by-parts boundary term vanishes at positive infinity
-- statement:
--   The endpoint term in stable Gamma integration by parts is (e^(-ux)-1) x^-alpha/(-alpha). As x→∞, the exponential tends to zero for u>0, so the first factor tends to -1; the power factor tends to zero for alpha>0 by Real.tendsto_rpow_neg_atTop, including its constant denominator. Their product tends to zero. This is the rigorous infinite-endpoint boundary condition of Kyprianou Exercise 1.4(i).
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4(i), printed solution p.301, PDF page 155.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
open Real Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaBoundaryAtInfinity
    (alpha u : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hu : 0 < u) :
    Filter.Tendsto
      (fun x : ℝ => (Real.exp (-(u * x)) - 1) * (x ^ (-alpha) / (-alpha)))
      Filter.atTop (nhds (0 : ℝ)) := by sorry
