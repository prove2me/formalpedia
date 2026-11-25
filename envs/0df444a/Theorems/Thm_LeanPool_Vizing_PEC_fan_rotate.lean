-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_fan_rotate
-- name    : LeanPool.Vizing.PEC.fan_rotate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:03:16.932851+00:00
-- url     : https://prove2.me/theorems/23c17c0b-cfdd-4b4d-8b58-878183746a22
-- title:
--   PEC: fan rotate
-- statement:
--   Rotating a fan: if some colour `b` is free both at `x` and at the last vertex of the fan,
--   then the uncoloured edge `x y` can be coloured (after recolouring the fan edges).
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Fan.lean#L54-L117
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Fan.lean#L54-L117

module
public import Definitions.Def_LeanPool_Vizing_Kempe
public import Definitions.Def_LeanPool_Vizing_Fan
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
open LeanPool.Vizing.PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}
omit [Fintype V] [DecidableEq V] [DecidableEq C]

theorem LeanPool.Vizing.PEC.fan_rotate (x y : V) (f : ℕ → V) : ∀ (n : ℕ) (c : PEC G C) (b : C), c.IsFan x y n f →
    c.IsFree x b → c.IsFree (f n) b → ∃ c' : PEC G C, Extends c c' ∧ c'.col x y ≠ none := by sorry
