-- Prove2me | Theorems.Thm_List_IsPrefix_head_eq
-- name    : List.IsPrefix.head_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:42.176205+00:00
-- url     : https://prove2.me/theorems/7725f63b-4fe1-4b47-881f-843815155ead
-- title:
--   Is Prefix: head eq
-- statement:
--   A prefix keeps the first entry.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L69-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L69-L74

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
open List

theorem List.IsPrefix.head_eq {α : Type*} {s t : List α} (h : s <+: t) (hne : s ≠ []) :
    t.head? = s.head? := by sorry
