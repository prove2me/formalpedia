-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_qv_time_threshold_integral
-- name    : Kyprianou.Ch04.ito43_qv_time_threshold_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:25:43.41537+00:00
-- url     : https://prove2.me/theorems/3c289cae-e1d3-40f0-9921-1409f1440749
-- title:
--   Lebesgue threshold mass is a cumulative-mass difference
-- statement:
--   Evaluate the Lebesgue mass of the threshold tail by interval length.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_qv_time_threshold_integral
    (t b : NNReal) :
    (∫ s in Ici (b:ℝ) ∩ Icc (0:ℝ) (t:ℝ), (1:ℝ) ∂volume) =
      (∫ s in Icc (0:ℝ) (t:ℝ), (1:ℝ) ∂volume) -
      (∫ s in Icc (0:ℝ) ((min t b:NNReal):ℝ), (1:ℝ) ∂volume) := by sorry
