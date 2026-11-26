-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41BoundarySplitV1
-- name    : Kyprianou.Ch04.exercise41BoundarySplitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:42:53.354012+00:00
-- url     : https://prove2.me/theorems/292256bf-a066-42df-9d34-9fc465eaec3b
-- title:
--   Decomposition of a function with a single possible discontinuity
-- statement:
--   Subtract the one-sided values to form a continuous part and represent the remaining difference by two indicators for the weak and strict positive half-lines.
-- source:
--   Kyprianou (2006), Exercise 4.1(i)–(ii), printed pp.105–106.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_smallTimeDriftLimit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04

theorem Kyprianou.Ch04.exercise41BoundarySplitV1
    (f fLeft fRight : ℝ → ℝ)
    (hLeft : ∀ x : ℝ, x < 0 → f x = fLeft x)
    (hRight : ∀ x : ℝ, 0 < x → f x = fRight x)
    (x : ℝ) :
    f x =
      (if x < 0 then fLeft x - fLeft 0
        else if 0 < x then fRight x - fRight 0 else 0) +
      fLeft 0 + (if 0 ≤ x then f 0 - fLeft 0 else 0) +
      (if 0 < x then fRight 0 - f 0 else 0) := by
  sorry
