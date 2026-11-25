-- Prove2me | Theorems.Thm_FractionalColouring_none_not_mem_shadows
-- name    : FractionalColouring.none_not_mem_shadows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:33:33.460887+00:00
-- url     : https://prove2.me/theorems/970d3d7c-f8ce-4ea0-b7e4-7d7003a8cb9d
-- title:
--   Fractional Colouring: none not mem shadows
-- statement:
--   The Fractional Colouring construction uses the none not mem shadows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L91-L92
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L91-L92

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

theorem FractionalColouring.none_not_mem_shadows : none ∉ (shadows : Finset (Vertex V)) := by sorry
