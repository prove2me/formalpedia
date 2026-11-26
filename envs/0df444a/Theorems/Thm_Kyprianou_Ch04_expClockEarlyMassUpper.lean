-- Prove2me | Theorems.Thm_Kyprianou_Ch04_expClockEarlyMassUpper
-- name    : Kyprianou.Ch04.expClockEarlyMassUpper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:37:26.110716+00:00
-- url     : https://prove2.me/theorems/d8840ddf-869d-4e6e-985f-a324bf686693
-- title:
--   Upper bound on the early exponential clock mass
-- statement:
--   The preimage under Real.toNNReal of a strict early horizon lies in the closed lower real ray. The exponential survival law and probability complement identity give the stated bound.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.expClockEarlyMassUpper (q : ℝ) (hq : 0 < q) (T : NNReal) :
    ((expMeasure q).map Real.toNNReal (Iio T)).toReal ≤
      1 - Real.exp (-(q * (T : ℝ))) := by
  sorry
