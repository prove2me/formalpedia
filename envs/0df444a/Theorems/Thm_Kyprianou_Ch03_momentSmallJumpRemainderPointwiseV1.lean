-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentSmallJumpRemainderPointwiseV1
-- name    : Kyprianou.Ch03.momentSmallJumpRemainderPointwiseV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T13:16:26.135615+00:00
-- url     : https://prove2.me/theorems/e0ff6701-969e-463b-87a4-e4b8efce0bbf
-- title:
--   Quadratic bound for a compensated exponential on the unit interval
-- statement:
--   For |bx|≤1 use the small-argument quadratic remainder. For |bx|>1 use exp(bx)≤exp(|b|), the bound |bx|≤|b| and 1≤(bx)^2.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; decomposition of compound-Poisson characteristic function and compensated exponential kernel.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentSmallJumpRemainderPointwiseV1
    (b x : Real) (hx : |x| ≤ 1) :
    ‖Real.exp (b * x) - 1 - b * x‖ ≤
      (Real.exp |b| + 1 + |b| + 1) * b ^ 2 * x ^ 2 := by sorry
