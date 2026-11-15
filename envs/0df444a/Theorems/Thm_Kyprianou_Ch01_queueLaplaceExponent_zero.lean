-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_zero
-- name    : Kyprianou.Ch01.queueLaplaceExponent_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:27:17.662387+00:00
-- url     : https://prove2.me/theorems/9fd7b7a9-dea3-48ab-920c-42bdd0b00745
-- title:
--   Kyprianou Exercise 1.9: the queue Laplace exponent vanishes at the origin
-- statement:
--   For any nonnegative claim arrival intensity and any service/claim-size measure, the unit-premium spectrally negative compound-Poisson queue Laplace exponent is zero at theta=0.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.9(i), target b284c2f7-67e4-4cda-a713-7bf561654166.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.queueLaplaceExponent_zero
    (rate : ℝ≥0) (F : Measure ℝ) :
    queueLaplaceExponent rate F 0 = 0 := by sorry
