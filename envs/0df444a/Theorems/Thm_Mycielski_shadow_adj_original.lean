-- Prove2me | Theorems.Thm_Mycielski_shadow_adj_original
-- name    : Mycielski.shadow_adj_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:23:46.191011+00:00
-- url     : https://prove2.me/theorems/42b1e638-7261-4d43-bcd2-51e1ea18f92c
-- title:
--   Mycielski: shadow adj original
-- statement:
--   The Mycielski construction uses the shadow adj original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L69-L70
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean#L69-L70

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

theorem Mycielski.shadow_adj_original {V : Type u} (G : SimpleGraph V) (v w : V) :
    (graph G).Adj (shadow v) (original w) ↔ G.Adj v w := by sorry
