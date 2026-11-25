-- Prove2me | Theorems.Thm_Mycielski_original_adj_shadow
-- name    : Mycielski.original_adj_shadow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:23:45.251505+00:00
-- url     : https://prove2.me/theorems/5588a1af-3c0c-40a0-bf51-6898717faf60
-- title:
--   Mycielski: original adj shadow
-- statement:
--   The Mycielski construction uses the original adj shadow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L66-L67
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L66-L67

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

theorem Mycielski.original_adj_shadow {V : Type u} (G : SimpleGraph V) (v w : V) :
    (graph G).Adj (original v) (shadow w) ↔ G.Adj v w := by sorry
