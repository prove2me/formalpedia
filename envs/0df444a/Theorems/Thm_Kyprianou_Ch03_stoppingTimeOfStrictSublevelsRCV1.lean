-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stoppingTimeOfStrictSublevelsRCV1
-- name    : Kyprianou.Ch03.stoppingTimeOfStrictSublevelsRCV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T11:02:25.639654+00:00
-- url     : https://prove2.me/theorems/7810e39f-2fe8-4be2-80be-91b000c72d3d
-- title:
--   Right-continuity converts strict sublevels to stopping time
-- statement:
--   Use decreasing positive offsets to express each closed sublevel as a countable intersection in every later sigma algebra, and then right continuity.
-- source:
--   Kyprianou (2006), Theorem 3.3, delayed open hitting stopping time.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.stoppingTimeOfStrictSublevelsRCV1
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hRC : F.IsRightContinuous) (T : Omega → WithTop NNReal)
    (hLt : ∀ s : NNReal, MeasurableSet[F s] {w | T w < (s : WithTop NNReal)}) :
    IsStoppingTime F T := by
  sorry
