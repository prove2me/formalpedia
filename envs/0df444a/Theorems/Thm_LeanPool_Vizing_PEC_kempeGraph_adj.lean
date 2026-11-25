-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_kempeGraph_adj
-- name    : LeanPool.Vizing.PEC.kempeGraph_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:55:17.200583+00:00
-- url     : https://prove2.me/theorems/af76df7e-d5ab-4143-91ac-e73a73cc671d
-- title:
--   PEC: kempe Graph adj
-- statement:
--   The PEC construction uses the kempe Graph adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Kempe.lean#L39-L40
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Kempe.lean#L39-L40

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
omit [Fintype V] [DecidableEq V] [DecidableEq C]

theorem LeanPool.Vizing.PEC.kempeGraph_adj {c : PEC G C} {a b : C} {u v : V} :
    (c.kempeGraph a b).Adj u v ↔ u ≠ v ∧ (c.col u v = some a ∨ c.col u v = some b) := by sorry
