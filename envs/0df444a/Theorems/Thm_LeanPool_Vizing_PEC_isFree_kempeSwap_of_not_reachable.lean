-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_isFree_kempeSwap_of_not_reachable
-- name    : LeanPool.Vizing.PEC.isFree_kempeSwap_of_not_reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:55:19.124905+00:00
-- url     : https://prove2.me/theorems/37ba6e40-1ed3-47c7-a94d-46f5c180cb1d
-- title:
--   PEC: is Free kempe Swap of not reachable
-- statement:
--   Off the Kempe component the free colours are unchanged.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Kempe.lean#L171-L179
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Kempe.lean#L171-L179

module
public import Definitions.Def_LeanPool_Vizing_Endpoints
public import Definitions.Def_LeanPool_Vizing_Kempe
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
open LeanPool.Vizing.PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}
omit [Fintype V] [DecidableEq V]

theorem LeanPool.Vizing.PEC.isFree_kempeSwap_of_not_reachable (c : PEC G C) (a b : C) {x v : V}
    (hv : ¬ (c.kempeGraph a b).Reachable x v) (γ : C) :
    (c.kempeSwap a b x).IsFree v γ ↔ c.IsFree v γ := by sorry
