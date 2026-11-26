-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cosine_clipped_prefix
-- name    : Kyprianou.Ch04.ito43_cosine_clipped_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:44:38.052458+00:00
-- url     : https://prove2.me/theorems/9827c9dd-8bcb-4d39-b7cb-c14983a13cf3
-- title:
--   Bounded mark sum differs from complete prefix by at most one term
-- statement:
--   The complete grid cells before the stopping time form an initial segment. At most one cell crosses the time, and its contribution lies between zero and the mark bound.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cosine_clipped_prefix (X : NNReal → ℝ) (q : ℝ → ℝ) (h0 : q 0 = 0)
    (C : ℝ) (hC : 0 ≤ C) (hq : ∀ z, 0 ≤ q z ∧ q z ≤ C)
    (T t : NNReal) (ht : t ≤ T) (n : ℕ) (hn : 0 < n) :
    let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    ∃ j ≤ n, |(t:ℝ)-(u j:ℝ)| ≤ (T:ℝ)/(n:ℝ) ∧
      |(∑ k ∈ Finset.range n, q (X (v (k+1))-X (v k))) -
       (∑ k ∈ Finset.range j, q (X (u (k+1))-X (u k)))| ≤ C := by sorry
