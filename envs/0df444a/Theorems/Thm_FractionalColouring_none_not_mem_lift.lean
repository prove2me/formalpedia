-- Prove2me | Theorems.Thm_FractionalColouring_none_not_mem_lift
-- name    : FractionalColouring.none_not_mem_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:33:12.318997+00:00
-- url     : https://prove2.me/theorems/d05bee55-61f7-45f4-a5b2-804419c82256
-- title:
--   Fractional Colouring: none not mem lift
-- statement:
--   The Fractional Colouring construction uses the none not mem lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L69-L70
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L69-L70

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

theorem FractionalColouring.none_not_mem_lift {s : Finset V} : none ∉ lift s := by sorry
