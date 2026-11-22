-- Prove2me | Theorems.Thm_Lean4LPD_Ladder_cumulation
-- name    : Lean4LPD.Ladder.cumulation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:06:10.552871+00:00
-- url     : https://prove2.me/theorems/e24d4038-a05d-46dd-81e9-db3ca34b7155
-- title:
--   Ladder: cumulation
-- statement:
--   **Single-jump cumulation.** Formalizes `apd:cor:norm_cumulation_jump` (i): after any `g`
--   Pauli rotations,
--
--     `N_{≥m}^{(g)} ≤ C(g, m) · a^m · M`,
--
--   where `a = sin(dt)` is the damping factor and `M = ‖O‖_{2,normalized}`.
--
--   The total mass enters with coefficient one: the base case `m = 0` is the reservoir bound
--   `N 0 g ≤ M`, valid for every `g`. The only sign hypothesis is `0 ≤ a`, used to multiply the
--   inductive hypothesis through the recursion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Recursion.lean#L71-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Recursion.lean#L71-L90

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

theorem Lean4LPD.Ladder.cumulation (ha : 0 ≤ a) :
    ∀ m g : ℕ, L.N m g ≤ (g.choose m : ℝ) * a ^ m * M := by sorry
