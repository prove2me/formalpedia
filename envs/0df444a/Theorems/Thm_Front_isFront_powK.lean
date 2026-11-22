-- Prove2me | Theorems.Thm_Front_isFront_powK
-- name    : Front.isFront_powK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:46.463144+00:00
-- url     : https://prove2.me/theorems/bc03716f-24e8-4e09-ba8c-623cfd5c3f6a
-- title:
--   Front: is Front pow K
-- statement:
--   **`[M]^k` the family of subsets of `M` of size `k` is a front on `M`.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L178-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L178-L206

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

theorem Front.isFront_powK {M : ℕ → ℕ} (hM : StrictMono M) (k : ℕ) : IsFront (powK M k) M := by sorry
