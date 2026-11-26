-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_mul_numClasses_le
-- name    : LeanPool.K5MinorFreeChoosability.mul_numClasses_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:17.389017+00:00
-- url     : https://prove2.me/theorems/f0fd8bc4-5694-5945-9194-724685b1dee4
-- title:
--   K5 Minor Free Choosability: mul num Classes le
-- statement:
--   Counting classes from below: if every class has at least `k` elements, then
--   `k * numClasses s ≤ |α|`.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L153-L177
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L153-L177

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}

theorem LeanPool.K5MinorFreeChoosability.mul_numClasses_le [Finite α] (s : Setoid α) (k : ℕ)
    (hk : ∀ a, k ≤ Nat.card {b // s a b}) : k * numClasses s ≤ Nat.card α := by sorry
