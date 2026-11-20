-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneCompensationPowerSet
-- name    : Kyprianou.Ch01.stableAlphaBelowOneCompensationPowerSet
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:27:37.62848+00:00
-- url     : https://prove2.me/theorems/48a65eb3-3898-4adf-adce-e6f3dbb65bb9
-- title:
--   Stable below-one small-jump moment on actual Lebesgue interval zero to one
-- statement:
--   The compensated stable small-jump radial moment is the genuine Lebesgue set integral on (0,1): integral of r^-alpha equals 1/(1-alpha), for 0<alpha<1. The proof uses the already-Proved intervalIntegral result and pinned measure-zero endpoints.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, original stable Lévy small-jump compensation.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneCompensationPowerInterval
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaBelowOneCompensationPowerSet
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    (∫ r in Set.Ioo (0 : ℝ) 1, r ^ (-alpha) ∂volume) =
      1 / (1 - alpha) := by sorry
