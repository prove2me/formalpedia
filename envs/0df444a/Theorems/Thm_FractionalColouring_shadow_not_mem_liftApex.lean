-- Prove2me | Theorems.Thm_FractionalColouring_shadow_not_mem_liftApex
-- name    : FractionalColouring.shadow_not_mem_liftApex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:33:15.953211+00:00
-- url     : https://prove2.me/theorems/3820bd56-b44b-4bfa-8786-b692b7fa5acd
-- title:
--   Fractional Colouring: shadow not mem lift Apex
-- statement:
--   The Fractional Colouring construction uses the shadow not mem lift Apex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L78-L79
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L78-L79

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

theorem FractionalColouring.shadow_not_mem_liftApex {s : Finset V} {v : V} : shadow v ∉ liftApex s := by sorry
