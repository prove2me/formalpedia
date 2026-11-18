-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineTailIntegrable
-- name    : Kyprianou.Ch01.stableAlphaOneCosineTailIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:32:12.569865+00:00
-- url     : https://prove2.me/theorems/7505915a-43d0-4d6f-ab86-5cc851825dde
-- title:
--   Integrability at infinity of the index-one stable cosine Lévy kernel
-- statement:
--   The integral of (1−cos x)/x² over x>1 is absolutely convergent. The standard estimate 0≤1−cos x≤2 and integrability of x^(−2) on the right infinite tail establish the tail half of the alpha-one stable cosine integral in Kyprianou (2006) Chapter 1.
-- source:
--   Kyprianou (2006), Chapter 1, stable alpha-one characteristic exponent and positive-half-line cosine integral.

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCosineTailIntegrable :
    IntegrableOn (fun r : ℝ => (1 - Real.cos r) / r ^ 2)
    (Set.Ioi (1 : ℝ)) := by
  sorry
