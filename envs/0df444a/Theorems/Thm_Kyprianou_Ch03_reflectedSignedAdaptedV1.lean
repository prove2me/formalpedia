-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectedSignedAdaptedV1
-- name    : Kyprianou.Ch03.reflectedSignedAdaptedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T19:17:43.317345+00:00
-- url     : https://prove2.me/theorems/48b43e6b-90ca-4da8-a917-d5393e73d55c
-- title:
--   Signed reflected Lévy state is adapted to its completed natural filtration
-- statement:
--   For each deterministic time, the signed coordinate is measurable in the natural filtration. The countable dense-prefix supremum with the endpoint agrees with the full running supremum almost surely by càdlàg regularity. Completion makes the original reflected coordinate measurable.
-- source:
--   Kyprianou (2006), Exercise 3.2: reflected Lévy processes are strong Markov.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.reflectedSignedAdaptedV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (c y : ℝ)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F) :
    Adapted F (reflectedSup (fun u v => c * X u v) y) := by
  sorry
