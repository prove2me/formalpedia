-- Prove2me | Theorems.Thm_FractionalColouring_isIndepSet_liftApex
-- name    : FractionalColouring.isIndepSet_liftApex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:34:30.298864+00:00
-- url     : https://prove2.me/theorems/9f72132a-0cc3-43f2-a5c5-7affc119a787
-- title:
--   Fractional Colouring: is Indep Set lift Apex
-- statement:
--   The Fractional Colouring construction uses the is Indep Set lift Apex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L112-L120
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L112-L120

module
public import Definitions.Def_FractionalLib_Basic
public import Definitions.Def_Mycielski_Basic
public import Definitions.Def_FractionalLib_LarsenProppUllman
set_option autoImplicit true
@[expose] public section
public section
open Finset hiding shadow
open Mycielski
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}

theorem FractionalColouring.isIndepSet_liftApex {s : Finset V} (hs : G.IsIndepSet (s : Set V)) :
    (graph G).IsIndepSet ((liftApex s : Finset (Vertex V)) : Set (Vertex V)) := by sorry
