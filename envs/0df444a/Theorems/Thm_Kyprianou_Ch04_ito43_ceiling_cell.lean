-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_ceiling_cell
-- name    : Kyprianou.Ch04.ito43_ceiling_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:26:11.287928+00:00
-- url     : https://prove2.me/theorems/5ca8daff-5f6c-5a28-a6fc-875ab80d2a07
-- title:
--   Right rounding equals the right endpoint in a grid cell
-- statement:
--   Right rounding equals the right endpoint in a grid cell.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
open Set
set_option autoImplicit false

/-- The right grid rounding equals the right endpoint throughout a half-open grid cell. -/

theorem Kyprianou.Ch04.ito43_ceiling_cell (T s : ℝ) (hT : 0 < T) (n k : ℕ) (hn : 0 < n)
    (hs : s ∈ Ioc (T * (k : ℝ) / (n : ℝ)) (T * ((k+1 : ℕ) : ℝ) / (n : ℝ))) :
    Nat.ceil (s * (n : ℝ) / T) = k+1 := by sorry
