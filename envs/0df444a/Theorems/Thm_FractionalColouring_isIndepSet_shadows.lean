-- Prove2me | Theorems.Thm_FractionalColouring_isIndepSet_shadows
-- name    : FractionalColouring.isIndepSet_shadows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:33:58.635309+00:00
-- url     : https://prove2.me/theorems/78376186-13ed-569c-bd5c-f73219758ae6
-- title:
--   Fractional Colouring: is Indep Set shadows
-- statement:
--   The Fractional Colouring construction uses the is Indep Set shadows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L122-L128
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L122-L128

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

theorem FractionalColouring.isIndepSet_shadows :
    (graph G).IsIndepSet ((shadows : Finset (Vertex V)) : Set (Vertex V)) := by sorry
