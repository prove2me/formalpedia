-- Prove2me | Theorems.Thm_FractionalColouring_original_mem_liftApex
-- name    : FractionalColouring.original_mem_liftApex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:33:12.236255+00:00
-- url     : https://prove2.me/theorems/84a8952d-6656-46ac-9981-efef302fa85a
-- title:
--   Fractional Colouring: original mem lift Apex
-- statement:
--   The Fractional Colouring construction uses the original mem lift Apex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L73-L75
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L73-L75

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

theorem FractionalColouring.original_mem_liftApex {s : Finset V} {v : V} :
    original v ∈ liftApex s ↔ v ∈ s := by sorry
