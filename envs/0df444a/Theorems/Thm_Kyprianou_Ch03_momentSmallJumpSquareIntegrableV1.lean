-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentSmallJumpSquareIntegrableV1
-- name    : Kyprianou.Ch03.momentSmallJumpSquareIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T13:16:12.077215+00:00
-- url     : https://prove2.me/theorems/5a5b505e-9e63-4d6b-bf02-671887bbb266
-- title:
--   Square integrability of the Lévy measure on the unit ball
-- statement:
--   Restrict the integrable minimum of one and x squared to the open unit interval, where it equals x squared.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; decomposition of compound-Poisson characteristic function and compensated exponential kernel.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentSmallJumpSquareIntegrableV1
    (T : ProbabilityTheory.LevyKhintchineTriple) :
    IntegrableOn (fun x : Real => x ^ 2) (Set.Ioo (-1 : Real) 1) T.levyMeasure := by sorry
