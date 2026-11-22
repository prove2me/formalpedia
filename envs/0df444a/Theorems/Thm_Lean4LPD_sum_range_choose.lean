-- Prove2me | Theorems.Thm_Lean4LPD_sum_range_choose
-- name    : Lean4LPD.sum_range_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:29.150228+00:00
-- url     : https://prove2.me/theorems/887c9879-3ee0-4d8c-8d11-5aaa903282d9
-- title:
--   Lean4 LPD: sum range choose
-- statement:
--   **Hockey-stick identity**, `range` form: `∑_{l < g} C(l, m) = C(g, m+1)`.
--
--   This is the identity used in `apd:cor:norm_cumulation_jump` to sum the
--   damped ladder recursion over rotations. Note both sides vanish for `g = 0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/HockeyStick.lean#L41-L48
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/HockeyStick.lean#L41-L48

module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.sum_range_choose (m : ℕ) :
    ∀ g : ℕ, ∑ l ∈ range g, l.choose m = g.choose (m + 1) := by sorry
