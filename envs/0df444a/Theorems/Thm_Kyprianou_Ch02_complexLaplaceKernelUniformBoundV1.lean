-- Prove2me | Theorems.Thm_Kyprianou_Ch02_complexLaplaceKernelUniformBoundV1
-- name    : Kyprianou.Ch02.complexLaplaceKernelUniformBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:49:47.929915+00:00
-- url     : https://prove2.me/theorems/0e39b78a-2de7-41a1-8e83-d36802d3dfa9
-- title:
--   complexLaplaceKernelUniformBound
-- statement:
--   complexLaplaceKernelUniformBound
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.complexLaplaceKernelUniformBoundV1
    (z : ℂ) (hz : 0 ≤ z.re) (x : ℝ) (hx : 0 ≤ x) :
    ‖1 - Complex.exp (-z * (x : ℂ))‖ ≤ 2 * max 1 ‖z‖ * min 1 |x| := by sorry
