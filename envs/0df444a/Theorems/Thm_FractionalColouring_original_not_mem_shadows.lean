-- Prove2me | Theorems.Thm_FractionalColouring_original_not_mem_shadows
-- name    : FractionalColouring.original_not_mem_shadows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:33:28.303805+00:00
-- url     : https://prove2.me/theorems/f34dfd84-f2c6-4f5f-9f43-3e67c3f33265
-- title:
--   Fractional Colouring: original not mem shadows
-- statement:
--   The Fractional Colouring construction uses the original not mem shadows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L85-L86
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L85-L86

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

theorem FractionalColouring.original_not_mem_shadows {v : V} : original v ∉ (shadows : Finset (Vertex V)) := by sorry
