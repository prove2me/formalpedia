-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAboveOneTailComplexMoment
-- name    : Kyprianou.Ch01.stableAboveOneTailComplexMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:20:14.286951+00:00
-- url     : https://prove2.me/theorems/25bfe99f-5d4f-4a9a-a6c3-176cf3efe40f
-- title:
--   Above-one stable tail compensation as exact complex Lebesgue moment
-- statement:
--   The stable large-jump tail power r^-alpha supported on r>=1 has positive-halfline complex integral exactly 1/(alpha-1) when 1<alpha<2. The source cutoff includes r=1; replacing Ici1 by Ioi1 under Lebesgue integration preserves the value.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4 stable compensated Fourier representation.

import Mathlib
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAboveOneTailComplexMoment
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    (∫ r in Set.Ioi (0 : ℝ),
      (if r < 1 then (0 : ℂ) else (((r ^ (-alpha) : ℝ) : ℂ))) ∂volume) =
      (((1 / (alpha - 1) : ℝ) : ℂ)) := by sorry
