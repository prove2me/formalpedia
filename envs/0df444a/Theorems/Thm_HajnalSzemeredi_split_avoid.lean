-- Prove2me | Theorems.Thm_HajnalSzemeredi_split_avoid
-- name    : HajnalSzemeredi.split_avoid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:46:58.455939+00:00
-- url     : https://prove2.me/theorems/83a4be45-b757-5bf3-8bf2-5436cf9f4eb3
-- title:
--   Hajnal Szemeredi: split avoid
-- statement:
--   `x ∈ T` y `x` alcanza un objetivo: si el camino pasa por `x'`, o lo evita o `x'` alcanza.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L64-L77
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L64-L77

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_HajnalSzemeredi_Structure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}

theorem HajnalSzemeredi.split_avoid {α : Type*} {R : α → α → Prop} {x z : α} :
    ∀ {a}, ReflTransGen R a z → a ≠ x →
      ReflTransGen (fun u v => R u v ∧ u ≠ x ∧ v ≠ x) a z ∨ ReflTransGen R x z := by sorry
