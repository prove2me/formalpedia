-- Prove2me | Theorems.Thm_Mycielski_cliqueFree_three_iff
-- name    : Mycielski.cliqueFree_three_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:23:55.793447+00:00
-- url     : https://prove2.me/theorems/8239c683-a0de-5846-b9c6-9d618def9dc1
-- title:
--   Mycielski: clique Free three iff
-- statement:
--   A triangle-free graph has no three pairwise adjacent vertices.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L101-L109
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L101-L109

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

theorem Mycielski.cliqueFree_three_iff {V : Type u} (G : SimpleGraph V) :
    G.CliqueFree 3 ↔ ∀ v w z, G.Adj v w → G.Adj v z → ¬ G.Adj w z := by sorry
