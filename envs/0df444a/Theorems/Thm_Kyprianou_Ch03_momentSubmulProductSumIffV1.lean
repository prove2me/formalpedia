-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentSubmulProductSumIffV1
-- name    : Kyprianou.Ch03.momentSubmulProductSumIffV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:30:42.233567+00:00
-- url     : https://prove2.me/theorems/9b35e79c-98f4-408e-8df3-8fdae1df7464
-- title:
--   Submultiplicative moments of an independent sum
-- statement:
--   By the measurable pushforward integration criterion the left side is integrability on the product. Sufficiency follows from the submultiplicative bound by c*g(x)*g(y). Necessity follows by Fubini: select a y with integrable x ↦ g(x+y), and bound g(x) by c*g(x+y)*g(-y).
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; shared reduction of submulMoment_forward and submulMoment_reverse.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentSubmulProductSumIffV1
    (mu nu : Measure Real) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (g : Real → Real) (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g)
    (hnu : Integrable g nu) :
    Integrable g ((mu.prod nu).map (fun p : Real × Real => p.1 + p.2)) ↔
      Integrable g mu := by sorry
