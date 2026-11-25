-- Prove2me | Theorems.Thm_FractionalColouring_original_mem_lift
-- name    : FractionalColouring.original_mem_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:32:58.217233+00:00
-- url     : https://prove2.me/theorems/14449b16-a4d9-4867-a6c3-aac30abdf862
-- title:
--   Fractional Colouring: original mem lift
-- statement:
--   The Fractional Colouring construction uses the original mem lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L61-L62
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L61-L62

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
omit [Fintype V]

theorem FractionalColouring.original_mem_lift {s : Finset V} {v : V} : original v ∈ lift s ↔ v ∈ s := by sorry
