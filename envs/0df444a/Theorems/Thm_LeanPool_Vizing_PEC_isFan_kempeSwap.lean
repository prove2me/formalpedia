-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_isFan_kempeSwap
-- name    : LeanPool.Vizing.PEC.isFan_kempeSwap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:03:32.176185+00:00
-- url     : https://prove2.me/theorems/12b3427f-b7a1-4180-993a-5a2ad74c53cd
-- title:
--   PEC: is Fan kempe Swap
-- statement:
--   A fan survives a Kempe interchange of `a` and `b` (where `a` is free at `x`) up to the first
--   index at which the fan edge is coloured `b` and the interchange separates `f i` from `x`.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Step.lean#L32-L74
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Step.lean#L32-L74

module
public import Definitions.Def_LeanPool_Vizing_Fan
public import Definitions.Def_LeanPool_Vizing_Step
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
open LeanPool.Vizing.PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [Fintype C] [DecidableEq C]
  {G : SimpleGraph V}
omit [Fintype V] [DecidableEq V] [Fintype C]

theorem LeanPool.Vizing.PEC.isFan_kempeSwap (c : PEC G C) {x y : V} {n : ℕ} {f : ℕ → V} (hfan : c.IsFan x y n f)
    {a b : C} (ha : c.IsFree x a) (w : V) {m : ℕ} (hm : m ≤ n)
    (hbreak : ∀ i < m, c.col x (f (i + 1)) = some b →
      ((c.kempeGraph a b).Reachable w (f i) ↔ (c.kempeGraph a b).Reachable w x)) :
    (c.kempeSwap a b w).IsFan x y m f := by sorry
