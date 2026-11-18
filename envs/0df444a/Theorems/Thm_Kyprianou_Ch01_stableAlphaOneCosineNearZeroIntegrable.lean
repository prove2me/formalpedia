-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineNearZeroIntegrable
-- name    : Kyprianou.Ch01.stableAlphaOneCosineNearZeroIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:35:22.323285+00:00
-- url     : https://prove2.me/theorems/6ec62680-ae4d-45ae-8d58-83ed51cfae96
-- title:
--   Local integrability of the stable-index-one cosine Lévy kernel near zero
-- statement:
--   The function (1−cos x)/x² is absolutely integrable over the interval 0<x<1. This follows from the exact Mathlib inequality 1−x²/2≤cos x, which bounds the nonnegative cosine kernel by 1/2, and the finite Lebesgue measure of (0,1). This is the near-origin half of Kyprianou Chapter 1 stable alpha-one cosine integral.
-- source:
--   Kyprianou (2006), Chapter 1, index-one stable cosine integral.

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCosineNearZeroIntegrable :
    IntegrableOn (fun r : ℝ => (1 - Real.cos r) / r ^ 2)
    (Set.Ioo (0 : ℝ) 1) := by
  sorry
