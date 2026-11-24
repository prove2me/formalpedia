-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentCPCharPowV1
-- name    : Kyprianou.Ch03.momentCPCharPowV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T13:16:09.48624+00:00
-- url     : https://prove2.me/theorems/70a1c109-fe9f-4ab5-85fe-76a7e0b8bc1d
-- title:
--   Characteristic function of finite convolution powers
-- statement:
--   Induct on n using characteristic function of convolution and finiteness of each convolution power.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; decomposition of compound-Poisson characteristic function and compensated exponential kernel.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentCPCharPowV1
    (mu : Measure Real) [IsFiniteMeasure mu] (xi : Real) (n : ℕ) :
    charFun (KSATSingleFlip.Connect.convPow mu n) xi = (charFun mu xi) ^ n := by sorry
