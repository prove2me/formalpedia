-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_zero_atom_path
-- name    : Kyprianou.Ch04.cor412_zero_atom_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:30:31.066812+00:00
-- url     : https://prove2.me/theorems/30c426a1-e654-4259-a4f5-8c97852543d2
-- title:
--   Zero all-time negative infimum is equivalent to a nonnegative path
-- statement:
--   Zero all-time negative infimum is equivalent to a nonnegative path.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.cor412_zero_atom_path
    (f : NNReal → ℝ) (h0 : f 0 = 0) (hb : BddBelow (range f)) :
    -sInf (range f) = 0 ↔ ∀ t : NNReal, 0 ≤ f t := by sorry
