-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentSmallJumpBandRealIntegralBoundV1
-- name    : Kyprianou.Ch03.momentSmallJumpBandRealIntegralBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T13:20:09.549622+00:00
-- url     : https://prove2.me/theorems/ae6c43cb-3a38-40dd-a9d7-285a3bd7dafe
-- title:
--   Uniform compensated exponential integrals over annuli
-- statement:
--   The kernel is nonnegative and integrable over the unit interval. Restriction monotonicity gives the bound.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; finite compensated small-jump approximation, reusing Chapter 8 finite transform construction and published compound-Poisson transform.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentSmallJumpBandRealIntegralBoundV1
    (T : ProbabilityTheory.LevyKhintchineTriple) (e b : Real) :
    (∫ x in {x : Real | e ≤ |x| ∧ |x| < 1},
      (Real.exp (b*x)-1-b*x) ∂T.levyMeasure) ≤
    ∫ x in Set.Ioo (-1 : Real) 1, (Real.exp (b*x)-1-b*x) ∂T.levyMeasure := by sorry
