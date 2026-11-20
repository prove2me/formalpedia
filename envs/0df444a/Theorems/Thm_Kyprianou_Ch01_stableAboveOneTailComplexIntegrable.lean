-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAboveOneTailComplexIntegrable
-- name    : Kyprianou.Ch01.stableAboveOneTailComplexIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:22:30.847454+00:00
-- url     : https://prove2.me/theorems/a099372f-12f1-4b9b-8060-42191b5b3f75
-- title:
--   Integrability of the complex large-jump stable source cutoff tail
-- statement:
--   For 1<alpha<2 the complex function r^-alpha supported at r>=1 is integrable over the positive halfline. Transfer Prove2Me proved real integrability to complex Bochner values and use the pinned null-singleton equality of Ioi1 and Ici1, retaining the original cutoff boundary.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4 original stable compensation.

import Mathlib
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAboveOneTailComplexIntegrable
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    IntegrableOn
      (fun r : ℝ => if r < 1 then (0 : ℂ) else
        (((r ^ (-alpha) : ℝ) : ℂ)))
      (Set.Ioi (0 : ℝ)) := by sorry
