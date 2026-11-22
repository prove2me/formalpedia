-- Prove2me | Theorems.Thm_Front_isFront_schreier
-- name    : Front.isFront_schreier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:47.597486+00:00
-- url     : https://prove2.me/theorems/0d418a5f-5e31-437a-ae9c-97bdc1de1cea
-- title:
--   Front: is Front schreier
-- statement:
--   **The Schreier front is a front on `M`.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L223-L255
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L223-L255

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

theorem Front.isFront_schreier {M : ℕ → ℕ} (hM : StrictMono M) : IsFront (schreier M) M := by sorry
