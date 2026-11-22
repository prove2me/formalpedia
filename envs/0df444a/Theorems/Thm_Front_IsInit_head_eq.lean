-- Prove2me | Theorems.Thm_Front_IsInit_head_eq
-- name    : Front.IsInit.head_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:46.036102+00:00
-- url     : https://prove2.me/theorems/3d198284-809b-405c-aeb6-dfdb7a9ad309
-- title:
--   Is Init: head eq
-- statement:
--   The first entry of a nonempty initial segment of `N` is `N 0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L107-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L107-L112

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

theorem Front.IsInit.head_eq {s : List ℕ} {N : ℕ → ℕ} (hs : IsInit s N) (hne : s ≠ []) :
    s.head? = some (N 0) := by sorry
