-- Prove2me | Theorems.Thm_Front_IsInit_getElem
-- name    : Front.IsInit.getElem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:49.742959+00:00
-- url     : https://prove2.me/theorems/f439850a-4202-4970-a9c1-5cb81372b50c
-- title:
--   Is Init: get Elem
-- statement:
--   The `i`-th entry of an initial segment of `N` is `N i`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L99-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L99-L104

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

theorem Front.IsInit.getElem {s : List ℕ} {N : ℕ → ℕ} (hs : IsInit s N)
    {i : ℕ} (h : i < s.length) : s[i] = N i := by sorry
