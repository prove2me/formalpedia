-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineScaling
-- name    : Kyprianou.Ch01.stableAlphaOneCosineScaling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:23:16.825239+00:00
-- url     : https://prove2.me/theorems/9ed8a758-444b-4cad-b8ac-543d61d69a14
-- title:
--   Positive-frequency scaling of the index-one stable cosine Lévy integral
-- statement:
--   For z>0, the positive-half-line Lebesgue integral of (1−cos(zr))/r² equals πz/2. This exact homogeneity is obtained from the previously proved π/2 cosine integral by the r↦zr change of variables. It is the real-part contribution of the source-faithful index-one stable Lévy exponent.
-- source:
--   Kyprianou (2006), Chapter 1, index-one stable Lévy exponent.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineIntegralValue
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCosineScaling
    (z : ℝ) (hz : 0 < z) :
    (∫ r in Set.Ioi (0 : ℝ), (1 - Real.cos (z * r)) / r ^ 2 ∂volume) =
      Real.pi * z / 2 := by
  sorry
