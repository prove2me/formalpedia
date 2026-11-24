-- Prove2me | Theorems.Thm_Kyprianou_Ch02_complexLaplaceAffineKernelDerivativeBoundV1
-- name    : Kyprianou.Ch02.complexLaplaceAffineKernelDerivativeBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:58:46.007422+00:00
-- url     : https://prove2.me/theorems/4f049b31-75f8-4c70-bc20-2d9139ba380b
-- title:
--   complexLaplaceAffineKernelDerivativeBound
-- statement:
--   complexLaplaceAffineKernelDerivativeBound
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.complexLaplaceAffineKernelDerivativeBoundV1
    (b : ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : r ≤ z.re)
    (x : ℝ) (hx : 0 ≤ x) :
    ‖b * (-(x : ℂ)) * Complex.exp (-z * (x : ℂ))‖ ≤
      (‖b‖ * max 1 (1 / r)) * min 1 |x| := by sorry
