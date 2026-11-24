-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovExtendedUpperGridV1
-- name    : Kyprianou.Ch03.strongMarkovExtendedUpperGridV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T07:41:35.718994+00:00
-- url     : https://prove2.me/theorems/6ff8b93e-0675-4cc3-8e57-14e72ebe0bba
-- title:
--   Extended stopping-time upper grids
-- statement:
--   Round each finite clock upward on a countable mesh of spacing 1/(n+1); assign zero at infinity. The finite-event fibres are differences of stopping sublevels at grid times.
-- source:
--   Kyprianou (2006), Theorem 3.1; parent f441c06a-283e-4064-b4f5-099f01124b30.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovExtendedUpperGridV1
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFiniteTime : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal)) :
    ∃ (T : ℕ → Omega → NNReal),
      (∀ n, Countable (Set.range (T n))) ∧
      (∀ n s, MeasurableSet[F s]
        ({w : Omega | tau w ≠ ⊤} ∩ {w | T n w = s})) ∧
      (∀ n w, tau w = ⊤ → T n w = 0) ∧
      (∀ w, tau w ≠ ⊤ → (∀ n, finiteTime w ≤ T n w) ∧
        Tendsto (fun n => T n w) atTop (nhds (finiteTime w))) := by
  sorry
