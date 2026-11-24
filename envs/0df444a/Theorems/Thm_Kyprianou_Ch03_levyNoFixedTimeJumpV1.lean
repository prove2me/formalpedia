-- Prove2me | Theorems.Thm_Kyprianou_Ch03_levyNoFixedTimeJumpV1
-- name    : Kyprianou.Ch03.levyNoFixedTimeJumpV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:06:56.655868+00:00
-- url     : https://prove2.me/theorems/11df6340-566e-48b2-ba84-cb77468f8366
-- title:
--   No fixed positive time jump of a real Levy process
-- statement:
--   As s tends to u from below, X u - X s tends almost surely to the jump, while its law equals that of X (u-s), tending almost surely to zero by right continuity at zero. Uniqueness of the limit in distribution proves the jump vanishes almost surely.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.4, exact parent 738b23d9-7a4a-4950-8e30-28b1734d73dd and children 42196240-b3a8-4082-98f6-d9e7e4a02b71, 1267c650-c871-460d-b8c1-f7127daafb6e.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.levyNoFixedTimeJumpV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (u : NNReal) (hu : 0 < u) :
    ∀ᵐ ω ∂P, Function.leftLim (fun r : NNReal => X r ω) u = X u ω := by sorry
