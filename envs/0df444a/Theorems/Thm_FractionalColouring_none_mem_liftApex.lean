-- Prove2me | Theorems.Thm_FractionalColouring_none_mem_liftApex
-- name    : FractionalColouring.none_mem_liftApex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:33:16.137797+00:00
-- url     : https://prove2.me/theorems/a9e8752d-696d-4ce1-a2cc-c05c0703cae4
-- title:
--   Fractional Colouring: none mem lift Apex
-- statement:
--   The Fractional Colouring construction uses the none mem lift Apex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L82-L83
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L82-L83

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

theorem FractionalColouring.none_mem_liftApex {s : Finset V} : none ∈ liftApex s := by sorry
