-- Prove2me | Theorems.Thm_Front_isInit_take
-- name    : Front.isInit_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:43.469899+00:00
-- url     : https://prove2.me/theorems/e3f4a245-b348-4117-bc37-bbd3b3181a2d
-- title:
--   Front: is Init take
-- statement:
--   The length-`n` initial segment of `N` is an initial segment of `N`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L95-L96
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L95-L96

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

theorem Front.isInit_take (N : ℕ → ℕ) (n : ℕ) : IsInit ((List.range n).map N) N := by sorry
