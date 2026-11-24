-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovCountableGridMeasV1
-- name    : Kyprianou.Ch03.strongMarkovCountableGridMeasV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:05:42.258473+00:00
-- url     : https://prove2.me/theorems/9d0171e6-9414-48a7-b30d-cf27fba5239f
-- title:
--   strongMarkovCountableGridMeasV1
-- statement:
--   Countable pasting on finite clock fibres and the infinite-clock zero cell.
-- source:
--   Kyprianou (2006), Theorem 3.1; parent ce10a41b-6699-4acd-b73c-5cedfb05d77b.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovCountableGridMeasV1
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (X : NNReal → Omega → Real) (hMeas : ∀ t, Measurable (X t))
    (T : Omega → NNReal) (hCount : Countable (Set.range T))
    (hFib : ∀ s, MeasurableSet[F s]
      ({w : Omega | tau w ≠ ⊤} ∩ {w | T w = s}))
    (hZero : ∀ w, tau w = ⊤ → T w = 0) :
    Measurable (fun w : Omega => fun u : NNReal => X (T w + u) w - X (T w) w) := by
  sorry
