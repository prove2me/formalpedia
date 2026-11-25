-- Prove2me | Theorems.Thm_FractionalColouring_isIndepSet_lift
-- name    : FractionalColouring.isIndepSet_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:33:36.476882+00:00
-- url     : https://prove2.me/theorems/319c1431-f181-5575-8c22-ac195b4aa646
-- title:
--   Fractional Colouring: is Indep Set lift
-- statement:
--   The Fractional Colouring construction uses the is Indep Set lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L96-L110
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L96-L110

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

theorem FractionalColouring.isIndepSet_lift {s : Finset V} (hs : G.IsIndepSet (s : Set V)) :
    (graph G).IsIndepSet ((lift s : Finset (Vertex V)) : Set (Vertex V)) := by sorry
