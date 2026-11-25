-- Prove2me | Theorems.Thm_Mycielski_apex_adj_shadow
-- name    : Mycielski.apex_adj_shadow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:23:53.719847+00:00
-- url     : https://prove2.me/theorems/557bba2a-f42d-499f-b25f-a553d6007864
-- title:
--   Mycielski: apex adj shadow
-- statement:
--   The Mycielski construction uses the apex adj shadow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L78-L79
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L78-L79

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

theorem Mycielski.apex_adj_shadow {V : Type u} (G : SimpleGraph V) (v : V) :
    (graph G).Adj none (shadow v) := by sorry
