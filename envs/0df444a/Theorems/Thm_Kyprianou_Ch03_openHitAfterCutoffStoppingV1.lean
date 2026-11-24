-- Prove2me | Theorems.Thm_Kyprianou_Ch03_openHitAfterCutoffStoppingV1
-- name    : Kyprianou.Ch03.openHitAfterCutoffStoppingV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T10:08:20.906069+00:00
-- url     : https://prove2.me/theorems/3fe1143f-d5e8-47dd-b497-a715784e3820
-- title:
--   Open hitting after a deterministic cutoff
-- statement:
--   On the almost surely right-continuous paths, the strict sublevel of the infimum of open-set hit times strictly after a is a countable union over rational witnesses in (a,s). Completion removes the exceptional null set, and right-continuity turns strict sublevels into stopping sublevels.
-- source:
--   Kyprianou (2006), Theorem 3.3; closed hitting child 567fb35e-7763-499a-b65a-6ab9d41e8485.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.openHitAfterCutoffStoppingV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hX : IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (B : Set Real) (hB : IsOpen B) (a : NNReal)
    (hRC : F.IsRightContinuous) :
    IsStoppingTime F (fun w : Omega => sInf {u : WithTop NNReal | ∃ r : NNReal,
        a < r ∧ X r w ∈ B ∧ u = (r : WithTop NNReal)}) := by
  sorry
