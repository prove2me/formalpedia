-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_uniform_sup_bound_limit
-- name    : Kyprianou.Ch04.ito43_uniform_sup_bound_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:55:03.9643+00:00
-- url     : https://prove2.me/theorems/78c94c2c-5de5-54e0-a0be-b7c77528ffc5
-- title:
--   Uniform smallness and boundedness control the real supremum
-- statement:
--   Each bounded supremum bounds the absolute errors. Uniform smallness bounds the supremum by an arbitrary positive tolerance, giving convergence to zero.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_uniform_sup_bound_limit (E : ℕ → NNReal → ℝ) (T : NNReal)
    (hb : ∀ n, BddAbove (Set.range (fun t : Set.Iic T => |E n t|)))
    (hE : ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ t ≤ T, |E n t| < e) :
    let C : ℕ → ℝ := fun n => sSup (Set.range (fun t : Set.Iic T => |E n t|))
    Tendsto C atTop (nhds 0) ∧ ∀ n t, t ≤ T → |E n t| ≤ |C n| := by sorry
