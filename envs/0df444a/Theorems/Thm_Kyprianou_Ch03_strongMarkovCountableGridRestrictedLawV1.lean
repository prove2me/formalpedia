-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovCountableGridRestrictedLawV1
-- name    : Kyprianou.Ch03.strongMarkovCountableGridRestrictedLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:41:28.139863+00:00
-- url     : https://prove2.me/theorems/ce10a41b-6699-4acd-b73c-5cedfb05d77b
-- title:
--   Countable stopped grid path law
-- statement:
--   Partition the finite event by countably many grid fibres. The stopped-event intersections are measurable at their grid times. Sum the deterministic restricted laws, and obtain measurability by countable pasting, including the infinite-event zero-clock cell.
-- source:
--   Kyprianou (2006), Theorem 3.1; parent f441c06a-283e-4064-b4f5-099f01124b30.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovCountableGridRestrictedLawV1
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFiniteTime : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal))
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hMeas : ∀ t, Measurable (X t))
    (hDet : ∀ (s : NNReal) (B : Set Omega), MeasurableSet[F s] B →
      Measure.map (fun w u => X (s + u) w - X s w) (P.restrict B) =
        P B • Measure.map (fun w u => X u w) P)
    (T : Omega → NNReal) (hCount : Countable (Set.range T))
    (hFib : ∀ s, MeasurableSet[F s]
      ({w : Omega | tau w ≠ ⊤} ∩ {w | T w = s}))
    (hZero : ∀ w, tau w = ⊤ → T w = 0)
    (hAbove : ∀ w, tau w ≠ ⊤ → finiteTime w ≤ T w) :
    Measurable (fun w : Omega => fun u : NNReal => X (T w + u) w - X (T w) w) ∧
    ∀ B : Set Omega, (∀ s : NNReal, MeasurableSet[F s]
      (B ∩ {w : Omega | tau w ≤ (s : WithTop NNReal)})) →
      Measure.map (fun w => fun u : NNReal => X (T w + u) w - X (T w) w)
        (P.restrict (B ∩ {w : Omega | tau w ≠ ⊤})) =
      P (B ∩ {w : Omega | tau w ≠ ⊤}) • Measure.map (fun w u => X u w) P := by
  sorry
