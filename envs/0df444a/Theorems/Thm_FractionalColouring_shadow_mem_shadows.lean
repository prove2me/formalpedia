-- Prove2me | Theorems.Thm_FractionalColouring_shadow_mem_shadows
-- name    : FractionalColouring.shadow_mem_shadows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:33:29.198997+00:00
-- url     : https://prove2.me/theorems/2b80b662-6b39-4d37-a5ec-eaed719a7c40
-- title:
--   Fractional Colouring: shadow mem shadows
-- statement:
--   The Fractional Colouring construction uses the shadow mem shadows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L88-L89
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L88-L89

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

theorem FractionalColouring.shadow_mem_shadows {v : V} : shadow v ∈ (shadows : Finset (Vertex V)) := by sorry
