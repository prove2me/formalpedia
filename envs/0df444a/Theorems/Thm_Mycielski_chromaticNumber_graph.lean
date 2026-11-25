-- Prove2me | Theorems.Thm_Mycielski_chromaticNumber_graph
-- name    : Mycielski.chromaticNumber_graph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:25:45.679307+00:00
-- url     : https://prove2.me/theorems/14514376-0086-5d57-9693-da02631b97f1
-- title:
--   Mycielski: chromatic Number graph
-- statement:
--   The chromatic number of a finite graph increases by exactly one.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Coloring.lean#L78-L103
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Coloring.lean#L78-L103

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

theorem Mycielski.chromaticNumber_graph {V : Type u} [Finite V] (G : SimpleGraph V) :
    (graph G).chromaticNumber = G.chromaticNumber + 1 := by sorry
