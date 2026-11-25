-- Prove2me | Theorems.Thm_Mycielski_colorable_of_colorable_succ
-- name    : Mycielski.colorable_of_colorable_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:25:43.394351+00:00
-- url     : https://prove2.me/theorems/a255e960-8248-5503-87b7-8743fda0f2b8
-- title:
--   Mycielski: colorable of colorable succ
-- statement:
--   Any `(k+1)`-coloring of the Mycielski graph yields a `k`-coloring of `G`.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Coloring.lean#L67-L70
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Coloring.lean#L67-L70

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

theorem Mycielski.colorable_of_colorable_succ {V : Type u} {G : SimpleGraph V} {k : ℕ}
    (h : (graph G).Colorable (k + 1)) : G.Colorable k := by sorry
