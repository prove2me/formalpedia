-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_exists_maximal_fan
-- name    : LeanPool.Vizing.PEC.exists_maximal_fan
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:03:27.105808+00:00
-- url     : https://prove2.me/theorems/ec0c3149-ee90-4001-837f-c94418628817
-- title:
--   PEC: exists maximal fan
-- statement:
--   Existence of a maximal fan.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Fan.lean#L121-L140
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Fan.lean#L121-L140

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

theorem LeanPool.Vizing.PEC.exists_maximal_fan [Finite V] (c : PEC G C) {x y : V}
    (hadj : G.Adj x y) (hnone : c.col x y = none) :
    ∃ (n : ℕ) (f : ℕ → V), c.IsFan x y n f ∧
      ∀ (m : ℕ) (g : ℕ → V), c.IsFan x y m g → m ≤ n := by sorry
