-- Prove2me | Theorems.Thm_Kyprianou_Ch06_finiteObservationTimesStrictGrid
-- name    : Kyprianou.Ch06.finiteObservationTimesStrictGrid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:57:50.084501+00:00
-- url     : https://prove2.me/theorems/8801a3d7-4a4e-4efd-8c9c-245fec677fab
-- title:
--   Lemma 6.18 temporal helper: finite observation times admit a strict ordered grid containing zero
-- statement:
--   For any finite list of nonnegative observation times, there exists a finite strictly increasing grid containing all distinct observation times and time zero. Construct it by ordering the finite set made from the observations and zero. This supplies the exact ordered-time partition needed to convert arbitrary overlapping Poisson count observations into compatible rectangle increments.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, finite time-grid refinement of outside-mark Poisson observations.

import Mathlib
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.finiteObservationTimesStrictGrid
    (m : Nat) (times : Fin m → NNReal) :
    ∃ (k : Nat) (grid : Fin k → NNReal),
      StrictMono grid ∧
      (∀ i : Fin m, ∃ j : Fin k, grid j = times i) ∧
      (∃ j : Fin k, grid j = 0) := by sorry
