-- Prove2me | Theorems.Thm_Konig_col_snd_of_kempe_path
-- name    : Konig.col_snd_of_kempe_path
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:11:20.51425+00:00
-- url     : https://prove2.me/theorems/be4f12d3-56fa-4e32-83e9-38330f690adc
-- title:
--   Konig: col snd of kempe path
-- statement:
--   **Alternation along a Kempe path.** If `b` is free at `y`, then on every path of the `a/b`
--   Kempe graph ending at `y`, the first edge has colour `a` if the length is odd and `b` if it is
--   even (and positive).
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Konig/Basic.lean#L76-L121
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Konig/Basic.lean#L76-L121

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

theorem Konig.col_snd_of_kempe_path (c : PEC G C) {a b : C} {y : V}
    (hy : c.IsFree y b) {u : V} (p : (c.kempeGraph a b).Walk u y) (hp : p.IsPath)
    (hlen : 0 < p.length) :
    c.col u p.snd = some (if p.length % 2 = 1 then a else b) := by sorry
