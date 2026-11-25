-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41LocallyFiniteCountRestrictionV1
-- name    : Kyprianou.Ch04.exercise41LocallyFiniteCountRestrictionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:56:32.565071+00:00
-- url     : https://prove2.me/theorems/c87f2a80-2a56-45f2-90c0-5bc94c5bcea5
-- title:
--   Locally finite point count agrees with a finite-horizon filter
-- statement:
--   If a set Z contains only finitely many marks up to horizon T, then the count of its marks up to each u≤T is exactly the cardinality of the finite-horizon mark set filtered by marks ≤u.
-- source:
--   Deterministic time-indexed counting lemma for Kyprianou (2006), Chapter 4, Exercise 4.1(i).

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41LocallyFiniteCountRestrictionV1
    (Z : Set NNReal) (T u : NNReal)
    (hZT : (Z ∩ Iic T).Finite) (hu : u ≤ T) :
    (Z ∩ Iic u).ncard =
      ((hZT.toFinset).filter (fun s => s ≤ u)).card := by
  sorry
