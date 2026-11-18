-- Prove2me | Theorems.Thm_Kyprianou_Ch06_finiteOrderedTimeGridCountTelescoping
-- name    : Kyprianou.Ch06.finiteOrderedTimeGridCountTelescoping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:15:54.163206+00:00
-- url     : https://prove2.me/theorems/1a945efe-552f-4ab5-a630-e84a38c6f024
-- title:
--   Lemma 6.18: exact integer count telescoping along a finite ordered time grid
-- statement:
--   For a nondecreasing sequence of k+1 nonnegative observation times beginning at zero and a nondecreasing integer counting function vanishing at zero, the count at the rth grid point equals the sum of consecutive count increments over the first r time intervals. This is the finite Fin-indexed temporal reconstruction required to construct compatible mark-time rectangles in Kyprianou (2006), Lemma 6.18.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, ordered observation-time count telescoping.

import Mathlib
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.finiteOrderedTimeGridCountTelescoping
    (k : Nat) (grid : Fin (k + 1) → NNReal)
    (hGrid : Monotone grid) (hZero : grid 0 = 0)
    (F : NNReal → Nat) (hF : Monotone F) (hFZero : F 0 = 0)
    (r : Nat) (hr : r ≤ k) :
    F (grid ⟨r, Nat.lt_succ_of_le hr⟩) =
      ∑ j ∈ (Finset.univ.filter (fun j : Fin k => j.val < r)),
        (F (grid j.succ) - F (grid j.castSucc)) := by sorry
