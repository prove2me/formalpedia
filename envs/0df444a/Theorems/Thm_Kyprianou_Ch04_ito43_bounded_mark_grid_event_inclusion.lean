-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_bounded_mark_grid_event_inclusion
-- name    : Kyprianou.Ch04.ito43_bounded_mark_grid_event_inclusion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:48:17.072803+00:00
-- url     : https://prove2.me/theorems/e09a7b8a-402a-50a0-a57a-1ce99c3fe73b
-- title:
--   Bounded mark grid error implies a large centred prefix
-- statement:
--   For any path and bounded nonnegative mark function, find the complete prefix by the clipped-grid lemma. Bound the prefix drift discrepancy by the full-grid mean error and one mesh width. The triangle inequality implies a large centred prefix whenever the stopped-grid error is large.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_bounded_mark_grid_event_inclusion (X : NNReal → ℝ) (q : ℝ → ℝ) (h0 : q 0 = 0)
    (T : NNReal) (c μ C e : ℝ) (he : 0 < e)
    (hC : 0 ≤ C) (hq : ∀ z, 0 ≤ q z ∧ q z ≤ C)
    (n : ℕ) (hn : 0 < n)
    (hmean : |(n:ℝ)*μ-c*(T:ℝ)| < e/4)
    (hmesh : |c| * ((T:ℝ)/(n:ℝ)) < e/4)
    (hcut : C < e/4) :
    let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
    ∀ t ≤ T, e ≤ |c*(t:ℝ)-∑ k ∈ Finset.range n,
        q (X (min t (u (k+1)))-X (min t (u k)))| →
      ∃ j ≤ n, e/4 ≤ |∑ k ∈ Finset.range j,
        (q (X (u (k+1))-X (u k))-μ)| := by sorry
