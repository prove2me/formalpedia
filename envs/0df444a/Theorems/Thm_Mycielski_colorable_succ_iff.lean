-- Prove2me | Theorems.Thm_Mycielski_colorable_succ_iff
-- name    : Mycielski.colorable_succ_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:25:53.202811+00:00
-- url     : https://prove2.me/theorems/b7d6a9b7-bb5a-41c3-ae47-5d8318eb7279
-- title:
--   Mycielski: colorable succ iff
-- statement:
--   Mycielski's coloring theorem, expressed using finite palettes.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Coloring.lean#L73-L75
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Coloring.lean#L73-L75

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

theorem Mycielski.colorable_succ_iff {V : Type u} (G : SimpleGraph V) (k : ℕ) :
    (graph G).Colorable (k + 1) ↔ G.Colorable k := by sorry
