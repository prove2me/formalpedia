-- Prove2me | Theorems.Thm_Kyprianou_Ch04_nestedGridKernelSquareV1
-- name    : Kyprianou.Ch04.nestedGridKernelSquareV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:55:13.320015+00:00
-- url     : https://prove2.me/theorems/520762ee-7c6b-409e-ab48-c47ff26dc20c
-- title:
--   nestedGridKernelSquareV1
-- statement:
--   nestedGridKernelSquareV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii), physical clipped-grid uniform cutoff estimate

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.nestedGridKernelSquareV1
    (a c K D x u v : ℝ) (hac : a ≤ c)
    (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hu : |u| ≤ K) (hd : |u-v| ≤ K*D) :
    (x * ((if a < |x| ∧ |x| < 1 then u else 0) -
      (if c < |x| ∧ |x| < 1 then v else 0)))^2 ≤
      K^2*D^2*(if c < |x| ∧ |x| < 1 then x^2 else 0) +
      K^2*(if a < |x| ∧ |x| ≤ c ∧ |x| < 1 then x^2 else 0) := by
  sorry
