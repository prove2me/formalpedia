-- Prove2me | Theorems.Thm_FractionalColouring_shadow_mem_lift
-- name    : FractionalColouring.shadow_mem_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:32:41.111178+00:00
-- url     : https://prove2.me/theorems/967e2cbb-5456-5cea-880d-4b87ee04026b
-- title:
--   Fractional Colouring: shadow mem lift
-- statement:
--   The Fractional Colouring construction uses the shadow mem lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L65-L66
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L65-L66

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

theorem FractionalColouring.shadow_mem_lift {s : Finset V} {v : V} : shadow v ∈ lift s ↔ v ∈ s := by sorry
