-- Prove2me | Theorems.Thm_Mycielski_card_vertex
-- name    : Mycielski.card_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:23:58.590544+00:00
-- url     : https://prove2.me/theorems/bcaf4b98-1c8e-5bdb-bf11-73efa90631f3
-- title:
--   Mycielski: card vertex
-- statement:
--   The construction adds one shadow per vertex and one apex.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L95-L98
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L95-L98

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Fintype.Option
public import Definitions.Def_Mycielski_Basic
set_option autoImplicit true
@[expose] public section
public section
open Mycielski
open SimpleGraph
universe u

theorem Mycielski.card_vertex {V : Type u} [Fintype V] :
    Fintype.card (Vertex V) = 2 * Fintype.card V + 1 := by sorry
