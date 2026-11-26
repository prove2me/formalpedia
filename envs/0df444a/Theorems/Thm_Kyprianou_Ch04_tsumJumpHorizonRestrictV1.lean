-- Prove2me | Theorems.Thm_Kyprianou_Ch04_tsumJumpHorizonRestrictV1
-- name    : Kyprianou.Ch04.tsumJumpHorizonRestrictV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:39:55.692082+00:00
-- url     : https://prove2.me/theorems/b1bce2b0-a86f-52a0-ae61-f31a33d1b282
-- title:
--   Restriction of a compact jump sum by a time indicator
-- statement:
--   Construct the subtype equivalence between the shorter time interval and the indicator support inside the larger horizon.
-- source:
--   Supporting proof for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.tsumJumpHorizonRestrictV1 (j : ℝ≥0 → ℝ) (t T : ℝ≥0) (ht : t ≤ T) :
    (∑' s : Ioc (0 : ℝ≥0) t, j s) =
      ∑' s : Ioc (0 : ℝ≥0) T,
        ((fun z : Ioc (0 : ℝ≥0) T => ((z : ℝ≥0) : ℝ)) ⁻¹' Iic (t : ℝ)).indicator
          (fun z => j z) s := by
  sorry
