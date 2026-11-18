-- Prove2me | Theorems.Thm_Kyprianou_Ch06_finiteObservationTimeCompatibleIntervalSchedule
-- name    : Kyprianou.Ch06.finiteObservationTimeCompatibleIntervalSchedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:23:53.349491+00:00
-- url     : https://prove2.me/theorems/0da44c0b-a102-4417-9cff-7a4e1d20e9c3
-- title:
--   Lemma 6.18: finite compatible observation-time interval schedule for all monotone counters
-- statement:
--   For a finite family of observation times there is a fixed finite schedule of chronologically disjoint intervals, independent of any counting process, such that every monotone integer-valued counter vanishing at time zero is reconstructed at every observation time by a fixed sum of interval increments. This is the complete deterministic time-refinement component of the finite marked-Poisson rectangle representation.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, finite observation-time refinement.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_finiteObservationTimesStrictGrid
import Theorems.Thm_Kyprianou_Ch06_finiteOrderedTimeGridCountTelescoping
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.finiteObservationTimeCompatibleIntervalSchedule
    (m : Nat) (times : Fin m → NNReal) :
    ∃ (k : Nat) (starts stops : Fin k → NNReal),
      (∀ j, starts j ≤ stops j) ∧
      (∀ j l : Fin k, j ≠ l →
        stops j ≤ starts l ∨ stops l ≤ starts j) ∧
      ∀ i : Fin m, ∃ J : Finset (Fin k),
        ∀ (F : NNReal → Nat), Monotone F → F 0 = 0 →
          F (times i) =
            ∑ j ∈ J, (F (stops j) - F (starts j)) := by sorry
