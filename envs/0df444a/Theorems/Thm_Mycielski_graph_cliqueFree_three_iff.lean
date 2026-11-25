-- Prove2me | Theorems.Thm_Mycielski_graph_cliqueFree_three_iff
-- name    : Mycielski.graph_cliqueFree_three_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:24:05.32368+00:00
-- url     : https://prove2.me/theorems/c9ea5bf9-8a9a-44c6-82f4-5ae19ce68468
-- title:
--   Mycielski: graph clique Free three iff
-- statement:
--   Triangle-freeness is both preserved and reflected.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L120-L127
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L120-L127

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

theorem Mycielski.graph_cliqueFree_three_iff {V : Type u} (G : SimpleGraph V) :
    (graph G).CliqueFree 3 ↔ G.CliqueFree 3 := by sorry
