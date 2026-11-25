-- Prove2me | Theorems.Thm_Mycielski_shadow_adj_apex
-- name    : Mycielski.shadow_adj_apex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:23:53.31098+00:00
-- url     : https://prove2.me/theorems/8840881b-b9a9-4690-918a-4e17331846d5
-- title:
--   Mycielski: shadow adj apex
-- statement:
--   The Mycielski construction uses the shadow adj apex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L75-L76
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L75-L76

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

theorem Mycielski.shadow_adj_apex {V : Type u} (G : SimpleGraph V) (v : V) :
    (graph G).Adj (shadow v) none := by sorry
