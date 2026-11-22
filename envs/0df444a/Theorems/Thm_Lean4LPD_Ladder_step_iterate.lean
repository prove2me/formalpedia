-- Prove2me | Theorems.Thm_Lean4LPD_Ladder_step_iterate
-- name    : Lean4LPD.Ladder.step_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:11.146797+00:00
-- url     : https://prove2.me/theorems/02563aa3-12c1-46da-87db-341b28e69359
-- title:
--   Ladder: step iterate
-- statement:
--   Iterating the flow recursion over the `g` steps, using `N m 0 = 0` for `m ≥ 1` to kill the
--   boundary term. This is the display `N^{(g)}_{≥m} ≤ sin(dt) ∑_{l=0}^{g-1} N^{(l)}_{≥m-1}` in the
--   proof of `apd:cor:norm_cumulation_jump`.
--
--   Note this needs no sign hypothesis on the damping factor `a`: the paper states the recursion
--   with `a = sin(dt) ≥ 0`, but the iteration itself is monotone regardless.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Recursion.lean#L49-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Recursion.lean#L49-L59

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Defs
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Recursion
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.Ladder
open Finset
variable {a M : ℝ} (L : Ladder a M)

theorem Lean4LPD.Ladder.step_iterate {m : ℕ} (hm : 1 ≤ m) :
    ∀ g : ℕ, L.N m g ≤ a * ∑ l ∈ range g, L.N (m - 1) l := by sorry
