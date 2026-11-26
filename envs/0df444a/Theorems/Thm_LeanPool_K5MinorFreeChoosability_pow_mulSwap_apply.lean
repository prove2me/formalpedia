-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_pow_mulSwap_apply
-- name    : LeanPool.K5MinorFreeChoosability.pow_mulSwap_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:10:59.97684+00:00
-- url     : https://prove2.me/theorems/787e5704-61fe-45e8-9044-6d8e2bdf33ba
-- title:
--   K5 Minor Free Choosability: pow mul Swap apply
-- statement:
--   Iterating `π * swap x y` from `y` follows the `π`-orbit of `x` as long as it avoids `x`
--   and `y`.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L283-L294
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L283-L294

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
variable [DecidableEq α]

theorem LeanPool.K5MinorFreeChoosability.pow_mulSwap_apply (π : Perm α) (x y : α) (m : ℕ)
    (hm : ∀ i, 0 < i → i < m → (π ^ i) x ≠ x ∧ (π ^ i) x ≠ y) :
    ∀ j, 0 < j → j ≤ m → ((π * swap x y) ^ j) y = (π ^ j) x := by sorry
