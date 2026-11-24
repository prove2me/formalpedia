-- Prove2me | Theorems.Thm_Kyprianou_Ch02_complexLaplaceAffineKernelDerivativeV1
-- name    : Kyprianou.Ch02.complexLaplaceAffineKernelDerivativeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:58:42.503245+00:00
-- url     : https://prove2.me/theorems/fdb49f4e-6b9f-471f-9ce2-e46d59bda6c6
-- title:
--   complexLaplaceAffineKernelDerivative
-- statement:
--   complexLaplaceAffineKernelDerivative
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.complexLaplaceAffineKernelDerivativeV1
    (a b z : ℂ) (x : ℝ) :
    HasDerivAt (fun w : ℂ => a + b * Complex.exp (-w * (x : ℂ)))
      (b * (-(x : ℂ)) * Complex.exp (-z * (x : ℂ))) z := by sorry
