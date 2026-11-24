-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovCountableGridSumLawV1
-- name    : Kyprianou.Ch03.strongMarkovCountableGridSumLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:05:40.970802+00:00
-- url     : https://prove2.me/theorems/c3eecd51-65d6-4b69-8b06-f11d1f543f7e
-- title:
--   strongMarkovCountableGridSumLawV1
-- statement:
--   Partition the stopped event into measurable countable grid fibres and sum the deterministic restricted laws.
-- source:
--   Kyprianou (2006), Theorem 3.1; parent ce10a41b-6699-4acd-b73c-5cedfb05d77b.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovCountableGridSumLawV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal)
    (finiteTime : Omega → NNReal)
    (hFiniteTime : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal))
    (X : NNReal → Omega → Real) (hMeas : ∀ t, Measurable (X t))
    (hDet : ∀ (s : NNReal) (B : Set Omega), MeasurableSet[F s] B →
      Measure.map (fun w u => X (s + u) w - X s w) (P.restrict B) =
        P B • Measure.map (fun w u => X u w) P)
    (T : Omega → NNReal) (hCount : Countable (Set.range T))
    (hFib : ∀ s, MeasurableSet[F s]
      ({w : Omega | tau w ≠ ⊤} ∩ {w | T w = s}))
    (hAbove : ∀ w, tau w ≠ ⊤ → finiteTime w ≤ T w)
    (hZ : Measurable (fun w : Omega => fun u : NNReal => X (T w + u) w - X (T w) w)) :
    ∀ B : Set Omega, (∀ s : NNReal, MeasurableSet[F s]
      (B ∩ {w : Omega | tau w ≤ (s : WithTop NNReal)})) →
      Measure.map (fun w => fun u : NNReal => X (T w + u) w - X (T w) w)
        (P.restrict (B ∩ {w : Omega | tau w ≠ ⊤})) =
      P (B ∩ {w : Omega | tau w ≠ ⊤}) • Measure.map (fun w u => X u w) P := by
  sorry
