-- Prove2me | Theorems.Thm_Konig_exists_free_of_none
-- name    : Konig.exists_free_of_none
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:09:50.395601+00:00
-- url     : https://prove2.me/theorems/eed36080-e948-4595-bcab-d8ebad0937e3
-- title:
--   Konig: exists free of none
-- statement:
--   At an endpoint of an uncoloured edge some colour is free, provided there are at least `Δ(G)`
--   colours.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Konig/Basic.lean#L36-L59
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Konig/Basic.lean#L36-L59

module
public import Definitions.Def_LeanPool_Vizing_Main
public import Definitions.Def_Konig_Basic
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Konig
open LeanPool.Vizing LeanPool.Vizing.PEC
variable {V : Type*} {C : Type*} {G : SimpleGraph V}

theorem Konig.exists_free_of_none [Fintype V] [Fintype C] [DecidableRel G.Adj] (c : PEC G C)
    (hcard : G.maxDegree ≤ Fintype.card C) {x y : V} (hadj : G.Adj x y)
    (hnone : c.col x y = none) : ∃ γ, c.IsFree x γ := by sorry
