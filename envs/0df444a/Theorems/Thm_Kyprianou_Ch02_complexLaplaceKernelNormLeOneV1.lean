-- Prove2me | Theorems.Thm_Kyprianou_Ch02_complexLaplaceKernelNormLeOneV1
-- name    : Kyprianou.Ch02.complexLaplaceKernelNormLeOneV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:49:49.357523+00:00
-- url     : https://prove2.me/theorems/925350f6-aaad-4a30-a364-899a6ea272a0
-- title:
--   complexLaplaceKernelNormLeOne
-- statement:
--   complexLaplaceKernelNormLeOne
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.complexLaplaceKernelNormLeOneV1
    (z : ℂ) (hz : 0 ≤ z.re) (x : ℝ) (hx : 0 ≤ x) :
    ‖Complex.exp (-z * (x : ℂ))‖ ≤ 1 := by sorry
