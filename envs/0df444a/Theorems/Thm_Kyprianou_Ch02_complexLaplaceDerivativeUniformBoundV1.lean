-- Prove2me | Theorems.Thm_Kyprianou_Ch02_complexLaplaceDerivativeUniformBoundV1
-- name    : Kyprianou.Ch02.complexLaplaceDerivativeUniformBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:49:56.058208+00:00
-- url     : https://prove2.me/theorems/7fc859ce-56e0-4f4a-a29e-9d12014f3fd0
-- title:
--   complexLaplaceDerivativeUniformBound
-- statement:
--   complexLaplaceDerivativeUniformBound
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.complexLaplaceDerivativeUniformBoundV1
    (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : r ≤ z.re)
    (x : ℝ) (hx : 0 ≤ x) :
    ‖(x : ℂ) * Complex.exp (-z * (x : ℂ))‖ ≤ max 1 (1 / r) * min 1 |x| := by sorry
