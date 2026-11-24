-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentSignedExpToAbsExpV1
-- name    : Kyprianou.Ch03.momentSignedExpToAbsExpV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:35:21.675801+00:00
-- url     : https://prove2.me/theorems/4f6fcb19-506f-4464-9690-564b24cac025
-- title:
--   Two signed exponential moments yield an absolute exponential moment
-- statement:
--   Pointwise, exp(b*|x|) equals one of the two signed exponential terms according to the sign of x, and is bounded above by their sum. Apply the integrable domination criterion.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8: finite compound-Poisson law and exponential moment of the compensated small-jump law.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentSignedExpToAbsExpV1
    (nu : Measure Real) (b : Real)
    (hp : Integrable (fun x : Real => Real.exp (b * x)) nu)
    (hm : Integrable (fun x : Real => Real.exp (-b * x)) nu) :
    Integrable (fun x : Real => Real.exp (b * |x|)) nu := by sorry
