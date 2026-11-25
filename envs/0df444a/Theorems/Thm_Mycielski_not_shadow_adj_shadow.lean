-- Prove2me | Theorems.Thm_Mycielski_not_shadow_adj_shadow
-- name    : Mycielski.not_shadow_adj_shadow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:23:48.456363+00:00
-- url     : https://prove2.me/theorems/bcd07503-4a9a-42e5-bf49-54111e9aa815
-- title:
--   Mycielski: not shadow adj shadow
-- statement:
--   The Mycielski construction uses the not shadow adj shadow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L72-L73
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L72-L73

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

theorem Mycielski.not_shadow_adj_shadow {V : Type u} (G : SimpleGraph V) (v w : V) :
    ¬ (graph G).Adj (shadow v) (shadow w) := by sorry
