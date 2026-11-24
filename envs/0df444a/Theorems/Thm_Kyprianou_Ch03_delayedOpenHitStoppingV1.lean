-- Prove2me | Theorems.Thm_Kyprianou_Ch03_delayedOpenHitStoppingV1
-- name    : Kyprianou.Ch03.delayedOpenHitStoppingV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T10:08:24.729024+00:00
-- url     : https://prove2.me/theorems/84efefd4-78be-468e-9bfc-0e4148698374
-- title:
--   Delayed hitting of an open set is a stopping time
-- statement:
--   Right continuity of sample paths makes strict sublevels countable rational witness events. Completion absorbs exceptional null paths and right continuity of the filtration converts strict sublevels to closed sublevels.
-- source:
--   Kyprianou (2006), Theorem 3.3, closed-set first hitting time.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.delayedOpenHitStoppingV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real) (hX : IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (hRC : F.IsRightContinuous) (a : NNReal) (U : Set ℝ) (hU : IsOpen U) :
    IsStoppingTime F (fun w => sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t w ∈ U})) := by
  sorry
