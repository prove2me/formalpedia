-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cadlag_left_compact_bound
-- name    : Kyprianou.Ch04.ito43_cadlag_left_compact_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:27:06.728539+00:00
-- url     : https://prove2.me/theorems/f8097c39-c0b3-5d4c-82a7-153134d3cf54
-- title:
--   Genuine positive left limits inherit compact path bounds
-- statement:
--   Genuine positive left limits inherit compact path bounds.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open Set Filter
open scoped NNReal Topology
set_option autoImplicit false

/-- A compact bound on the path bounds every genuine positive left limit on that horizon. -/

theorem Kyprianou.Ch04.ito43_cadlag_left_compact_bound (X L : NNReal → ℝ) (T : NNReal) (M : ℝ)
    (hX : ∀ t ≤ T, |X t| ≤ M)
    (hL : ∀ t : NNReal, 0 < t → Tendsto X (nhdsWithin t (Iio t)) (nhds (L t))) :
    ∀ t : NNReal, 0 < t → t ≤ T → |L t| ≤ M := by sorry
