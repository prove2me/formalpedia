-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectionStoppedStateCutsMeasurableV1
-- name    : Kyprianou.Ch03.reflectionStoppedStateCutsMeasurableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:00:39.273074+00:00
-- url     : https://prove2.me/theorems/6023353f-66ed-476e-a96f-8b58e619212f
-- title:
--   Reflected state is measurable at finite stopping-time cuts
-- statement:
--   Countable observations of a càdlàg path give the reflected state at bounded stopped clocks. The completed filtration absorbs exceptional null sets.
-- source:
--   Kyprianou (2006), Exercise 3.2, stopped-state strong Markov transition kernel.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.reflectionStoppedStateCutsMeasurableV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F)
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFinite : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal))
    (c y : ℝ) :
    ∀ B : Set ℝ, MeasurableSet B → ∀ s : NNReal,
      MeasurableSet[F s]
        ({w | reflectedSup (fun u v => c * X u v) y (finiteTime w) w ∈ B}
          ∩ {w | tau w ≤ (s : WithTop NNReal)}) := by sorry
