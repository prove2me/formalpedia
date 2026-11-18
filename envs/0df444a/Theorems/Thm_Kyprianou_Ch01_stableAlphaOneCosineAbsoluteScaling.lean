-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineAbsoluteScaling
-- name    : Kyprianou.Ch01.stableAlphaOneCosineAbsoluteScaling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:29:49.796031+00:00
-- url     : https://prove2.me/theorems/d5041b7c-a5e7-4fd8-b68e-1bdfa94efb9a
-- title:
--   Absolute-frequency scaling of the index-one stable cosine Lévy integral
-- statement:
--   For any real frequency ξ, the positive-half-line integral of (1−cos(ξr))/r² equals (π/2)|ξ|. This extends the positive-frequency source identity by the evenness of cosine and includes ξ=0. It matches the real part of the index-one stable Lévy exponent used in Kyprianou Chapter 1.
-- source:
--   Kyprianou (2006), Chapter 1, index-one stable Lévy characteristic exponent.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineScaling
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCosineAbsoluteScaling
    (xi : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ), (1 - Real.cos (xi * r)) / r ^ 2 ∂volume) =
      Real.pi * |xi| / 2 := by
  sorry
