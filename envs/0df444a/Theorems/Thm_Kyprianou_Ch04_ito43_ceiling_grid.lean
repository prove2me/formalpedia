-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_ceiling_grid
-- name    : Kyprianou.Ch04.ito43_ceiling_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:19:03.608153+00:00
-- url     : https://prove2.me/theorems/ca494a76-4eb0-5627-9eea-93f150a0ebad
-- title:
--   Uniform right grid rounding bounds
-- statement:
--   Uniform right grid rounding bounds.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
open Filter Set
open scoped Topology
set_option autoImplicit false

/-- Right grid rounding stays within one mesh of the original time and below the horizon. -/

theorem Kyprianou.Ch04.ito43_ceiling_grid (T s : ℝ) (hT : 0 < T) (hs : s ∈ Icc 0 T)
    (n : ℕ) (hn : 0 < n) :
    let r := T * (Nat.ceil (s * (n : ℝ) / T) : ℝ) / (n : ℝ)
    s ≤ r ∧ r ≤ T ∧ r ≤ s + T / (n : ℝ) := by sorry
