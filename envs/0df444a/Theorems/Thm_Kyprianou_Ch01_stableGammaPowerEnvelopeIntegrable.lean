-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaPowerEnvelopeIntegrable
-- name    : Kyprianou.Ch01.stableGammaPowerEnvelopeIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:04:28.769751+00:00
-- url     : https://prove2.me/theorems/a3d5d3bd-c251-4969-974c-ce147acde0b2
-- title:
--   Integrable positive power-law envelope for the stable Gamma deficit near zero and infinity
-- statement:
--   For alpha in (0,1), the exponential deficit in the stable Gamma integral is dominated in absolute value by u*x^(-alpha) near zero and by x^(-alpha-1) above one. The piecewise positive envelope is integrable by Mathlib intervalIntegral.intervalIntegrable_rpow' on (0,1] and integrableOn_Ioi_rpow_of_lt on (1,∞). This rigorous local/tail bound is the key integrability step of the integration-by-parts child in Kyprianou Exercise 1.4(i).
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4(i), printed solution p.301, PDF p.155.

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
open MeasureTheory Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaPowerEnvelopeIntegrable
    (alpha u : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hu : 0 < u) :
    IntegrableOn (fun x : ℝ =>
      if x ≤ 1 then u * x ^ (-alpha) else x ^ (-alpha - 1))
      (Set.Ioi (0 : ℝ)) := by sorry
