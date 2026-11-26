-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_tail_law_eval
-- name    : Kyprianou.Ch04.cor412_tail_law_eval
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:40:38.955663+00:00
-- url     : https://prove2.me/theorems/9e621056-15b1-5813-bf2d-29b5775b8f95
-- title:
--   Integrated-tail law interval evaluation
-- statement:
--   The reflected integrated-tail measure evaluated on the deficit threshold interval equals the real integrated tail, assuming finite interval mass.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal
set_option autoImplicit false

/-- Evaluate the reflected positive-half-line density on a lower-deficit interval. -/

theorem Kyprianou.Ch04.cor412_tail_law_eval (ν : Measure ℝ) (d x : ℝ) (hd : 0 < d) (hx : 0 ≤ x)
    (hfin : ((volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun y : ℝ => ENNReal.ofReal (1/d) * ν (Iio (-y)))) (Iic x) ≠ ⊤) :
    (((volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun y : ℝ => ENNReal.ofReal (1/d) * ν (Iio (-y)))).map
      (fun y => -y) (Ici (-x))).toReal =
      (1/d) * ∫ y in Icc 0 x, (ν (Iio (-y))).toReal ∂volume := by sorry
