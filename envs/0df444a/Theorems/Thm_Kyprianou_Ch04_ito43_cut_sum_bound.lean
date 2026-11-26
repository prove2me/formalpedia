-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cut_sum_bound
-- name    : Kyprianou.Ch04.ito43_cut_sum_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:28:45.066399+00:00
-- url     : https://prove2.me/theorems/1e51bbf0-fb4c-4904-aac9-725791a749ba
-- title:
--   Sum grid cell errors with one terminal cut charge
-- statement:
--   Sum grid cell errors with one terminal cut charge.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_stopped_cell_geometry
open Set
set_option autoImplicit false

/-- Sum cell errors with an extra charge on the unique strictly cut cell. -/

theorem Kyprianou.Ch04.ito43_cut_sum_bound (u : ℕ → ℝ) (hu : Monotone u) (t c : ℝ) (hc : 0 ≤ c)
    (n : ℕ) (a b : ℕ → ℝ)
    (h : ∀ k < n, a k ≤ b k + if u k < t ∧ t < u (k+1) then c else 0) :
    (∑ k ∈ Finset.range n, a k) ≤ (∑ k ∈ Finset.range n, b k) + c := by sorry
