-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_eq_restrict
-- name    : LeanPool.K5MinorFreeChoosability.numClasses_eq_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:25.005082+00:00
-- url     : https://prove2.me/theorems/c7841509-a119-558d-ae16-11b3fcb6b9a3
-- title:
--   K5 Minor Free Choosability: num Classes eq restrict
-- statement:
--   Restricting to a subset `p` whose complement consists of singleton classes.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L180-L216
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L180-L216

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}

theorem LeanPool.K5MinorFreeChoosability.numClasses_eq_restrict (s : Setoid α) (p : α → Prop) (t : Setoid (Subtype p))
    (ht : ∀ a b : Subtype p, t a b ↔ s a b) (hout : ∀ a b, ¬ p a → s a b → a = b)
    [Finite α] :
    numClasses s = numClasses t + Nat.card {x // ¬ p x} := by sorry
