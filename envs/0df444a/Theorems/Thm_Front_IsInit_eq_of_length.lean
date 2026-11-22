-- Prove2me | Theorems.Thm_Front_IsInit_eq_of_length
-- name    : Front.IsInit.eq_of_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:44.805068+00:00
-- url     : https://prove2.me/theorems/3b252f9e-4d52-4793-9456-6cf3b6c73dd0
-- title:
--   Is Init: eq of length
-- statement:
--   An initial segment is determined by its length: two initial segments of `N` of equal length
--   are equal.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L116-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L116-L118

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

theorem Front.IsInit.eq_of_length {s t : List ℕ} {N : ℕ → ℕ}
    (hs : IsInit s N) (ht : IsInit t N) (h : s.length = t.length) : s = t := by sorry
