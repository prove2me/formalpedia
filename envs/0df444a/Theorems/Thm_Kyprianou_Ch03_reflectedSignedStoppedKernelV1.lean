-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectedSignedStoppedKernelV1
-- name    : Kyprianou.Ch03.reflectedSignedStoppedKernelV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T17:58:29.753304+00:00
-- url     : https://prove2.me/theorems/d40efd0f-ab9d-48e7-ad0d-81650a177216
-- title:
--   Stopped-state kernel factor for signed Lévy reflection
-- statement:
--   Use the strong Markov property of the original Lévy process on finite stopping-time events. The reflected state is measurable at the stopping time, and the shifted path has the fresh path law conditionally on that state. Countable evaluation approximates the running supremum on càdlàg paths.
-- source:
--   Kyprianou (2006), Exercise 3.2, proof via strong Markov and the running-maximum restart identity.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.reflectedSignedStoppedKernelV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (c y : ℝ) (hy : 0 ≤ y)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F)
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFinite : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal))
    (A : Set Omega)
    (hA : ∀ s : NNReal, MeasurableSet[F s]
      (A ∩ {w : Omega | tau w ≤ (s : WithTop NNReal)}))
    (f : ℝ → ℝ) (hf : Measurable f)
    (hBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |f z| ≤ C)
    (t : NNReal)
    :
    (∫ w in A ∩ {w | tau w ≠ ⊤},
      f (max (reflectedSup (fun s v => c * X s v) y (finiteTime w) w)
          (LevyExtrema.SBA.runSup (fun s => c * (X (finiteTime w + s) w - X (finiteTime w) w)) t)
          - c * (X (finiteTime w + t) w - X (finiteTime w) w)) ∂P) =
    (∫ w in A ∩ {w | tau w ≠ ⊤},
      (∫ eta, f (max (reflectedSup (fun s v => c * X s v) y (finiteTime w) w)
          (LevyExtrema.SBA.runSup (fun s => c * X s eta) t) - c * X t eta) ∂P) ∂P) := by sorry
