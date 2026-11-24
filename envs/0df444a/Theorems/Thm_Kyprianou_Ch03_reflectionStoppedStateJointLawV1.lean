-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectionStoppedStateJointLawV1
-- name    : Kyprianou.Ch03.reflectionStoppedStateJointLawV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T21:47:28.654504+00:00
-- url     : https://prove2.me/theorems/e016a264-f0b6-41b4-8edc-0713a3b7b97a
-- title:
--   Joint law of stopped state and fresh path
-- statement:
--   On rectangles, apply the restricted strong Markov identity to intersections with stopped-state preimages.
-- source:
--   Kyprianou (2006), Exercise 3.2, stopped-state kernel proof.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.reflectionStoppedStateJointLawV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F)
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFinite : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal))
    (A : Set Omega)
    (hA : ∀ s : NNReal, MeasurableSet[F s]
      (A ∩ {w | tau w ≤ (s : WithTop NNReal)}))
    (S : Omega → ℝ)
    (hS : ∀ B : Set ℝ, MeasurableSet B → ∀ s : NNReal,
      MeasurableSet[F s] ({w | S w ∈ B} ∩ {w | tau w ≤ (s : WithTop NNReal)}))
    :
    Measure.map (fun w => (S w, (fun w u => X (finiteTime w + u) w - X (finiteTime w) w) w)) (P.restrict (A ∩ {w | tau w ≠ ⊤})) =
      (Measure.map S (P.restrict (A ∩ {w | tau w ≠ ⊤}))).prod (Measure.map (fun w u => X u w) P) := by sorry
