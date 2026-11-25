-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_kempe_degree_le_one_of_isFree
-- name    : LeanPool.Vizing.PEC.kempe_degree_le_one_of_isFree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:02:20.965881+00:00
-- url     : https://prove2.me/theorems/eb3911c1-7286-4565-850e-a743223c29c1
-- title:
--   PEC: kempe degree le one of is Free
-- statement:
--   The PEC construction uses the kempe degree le one of is Free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Kempe.lean#L216-L233
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Kempe.lean#L216-L233

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
omit [DecidableEq V] [DecidableEq C]

theorem LeanPool.Vizing.PEC.kempe_degree_le_one_of_isFree (c : PEC G C) {a b : C} [DecidableRel (c.kempeGraph a b).Adj]
    {v : V} {γ : C} (hγ : γ = a ∨ γ = b) (hfree : c.IsFree v γ) :
    (c.kempeGraph a b).degree v ≤ 1 := by sorry
