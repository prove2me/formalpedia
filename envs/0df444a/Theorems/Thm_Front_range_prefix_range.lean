-- Prove2me | Theorems.Thm_Front_range_prefix_range
-- name    : Front.range_prefix_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:45.777628+00:00
-- url     : https://prove2.me/theorems/da63a1f0-fbba-4053-b04b-d2a5a0623281
-- title:
--   Front: range prefix range
-- statement:
--   `List.range` is monotone for the prefix order.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L87-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L87-L90

module
public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.Widget.Calc
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
open Front

theorem Front.range_prefix_range {m n : ℕ} (h : m ≤ n) : List.range m <+: List.range n := by sorry
