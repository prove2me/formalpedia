-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_isFree_kempeSwap_of_reachable
-- name    : LeanPool.Vizing.PEC.isFree_kempeSwap_of_reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:54:05.116913+00:00
-- url     : https://prove2.me/theorems/633782f0-796b-4cd4-bc81-92d3233afc32
-- title:
--   PEC: is Free kempe Swap of reachable
-- statement:
--   On the Kempe component the free colours get swapped.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Kempe.lean#L150-L167
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Kempe.lean#L150-L167

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

theorem LeanPool.Vizing.PEC.isFree_kempeSwap_of_reachable (c : PEC G C) (a b : C) {x v : V}
    (hv : (c.kempeGraph a b).Reachable x v) (γ : C) :
    (c.kempeSwap a b x).IsFree v γ ↔ c.IsFree v (Equiv.swap a b γ) := by sorry
