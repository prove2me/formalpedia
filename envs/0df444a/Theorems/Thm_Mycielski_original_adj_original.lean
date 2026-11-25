-- Prove2me | Theorems.Thm_Mycielski_original_adj_original
-- name    : Mycielski.original_adj_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:23:39.531329+00:00
-- url     : https://prove2.me/theorems/54eb1eee-1707-5c73-83d0-c355594f54e2
-- title:
--   Mycielski: original adj original
-- statement:
--   The Mycielski construction uses the original adj original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L63-L64
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L63-L64

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

theorem Mycielski.original_adj_original {V : Type u} (G : SimpleGraph V) (v w : V) :
    (graph G).Adj (original v) (original w) ↔ G.Adj v w := by sorry
