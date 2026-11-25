-- Prove2me | Theorems.Thm_Mycielski_colorable_succ
-- name    : Mycielski.colorable_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:25:54.074366+00:00
-- url     : https://prove2.me/theorems/e1705597-6fc2-4a7f-955d-e960a69943b1
-- title:
--   Mycielski: colorable succ
-- statement:
--   The extra color suffices for the Mycielski graph.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Coloring.lean#L40-L43
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Coloring.lean#L40-L43

module
public import Definitions.Def_Mycielski_Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Definitions.Def_Mycielski_Coloring
set_option autoImplicit true
@[expose] public section
public section
open Mycielski
open SimpleGraph
universe u v

theorem Mycielski.colorable_succ {V : Type u} {G : SimpleGraph V} {k : ℕ}
    (h : G.Colorable k) : (graph G).Colorable (k + 1) := by sorry
