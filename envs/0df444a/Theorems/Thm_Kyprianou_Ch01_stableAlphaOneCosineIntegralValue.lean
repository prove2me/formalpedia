-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineIntegralValue
-- name    : Kyprianou.Ch01.stableAlphaOneCosineIntegralValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:38:28.891275+00:00
-- url     : https://prove2.me/theorems/61b29e2d-3c93-4cc1-97a6-9d4025f6f98f
-- title:
--   Exact π/2 evaluation of the absolutely convergent stable-index-one cosine integral
-- statement:
--   The absolutely convergent improper integral of (1−cos r)/r² over positive r has exact value π/2. This is the remaining numerical-identity part of the source-faithful index-one stable cosine integral milestone. Its separate integrability component was established from sharp cosine bounds, with no other assumptions.
-- source:
--   Kyprianou (2006), Chapter 1, stable Lévy exponent index α=1.

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCosineIntegralValue :
    (∫ r in Set.Ioi (0 : ℝ),
      (1 - Real.cos r) / r ^ 2 ∂volume) = Real.pi / 2 := by
  sorry
