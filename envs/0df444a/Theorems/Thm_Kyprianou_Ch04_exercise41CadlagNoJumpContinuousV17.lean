-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41CadlagNoJumpContinuousV17
-- name    : Kyprianou.Ch04.exercise41CadlagNoJumpContinuousV17
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:13:32.207362+00:00
-- url     : https://prove2.me/theorems/6856ee67-988c-5d8a-b421-7a610c0c8e53
-- title:
--   Cadlag function with no jumps in a half-open interval is continuous on the closed interval
-- statement:
--   Cadlag function with no jumps in a half-open interval is continuous on the closed interval
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41CadlagNoJumpContinuousV17
    (f : NNReal → ℝ)
    (hR : ∀ u, ContinuousWithinAt f (Ici u) u)
    (hL : ∀ u, 0 < u → Tendsto f (nhdsWithin u (Iio u)) (nhds (Function.leftLim f u)))
    (s t : NNReal)
    (hJump : ∀ u ∈ Ioc s t, f u - Function.leftLim f u = 0) :
    ContinuousOn f (Icc s t) := by
  sorry
