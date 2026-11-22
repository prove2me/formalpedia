-- Prove2me | Theorems.Thm_Front_rangeMap_mem_powK
-- name    : Front.rangeMap_mem_powK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:47.867537+00:00
-- url     : https://prove2.me/theorems/0f6d1016-bfc8-4a41-9771-d94f8e0fa0c1
-- title:
--   Front: range Map mem pow K
-- statement:
--   The first `k` values of `M ∘ e` forms a size-`k` subset of `M`, for `e` strictly
--   monotone. This is the generic member of `[M]^k` used to witness Base and Density.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L167-L175
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean#L167-L175

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

theorem Front.rangeMap_mem_powK {M : ℕ → ℕ} (hM : StrictMono M) {e : ℕ → ℕ}
    (he : StrictMono e) (k : ℕ) : (List.range k).map (M ∘ e) ∈ powK M k := by sorry
