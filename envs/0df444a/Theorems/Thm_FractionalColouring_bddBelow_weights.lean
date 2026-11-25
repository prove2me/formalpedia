-- Prove2me | Theorems.Thm_FractionalColouring_bddBelow_weights
-- name    : FractionalColouring.bddBelow_weights
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:29:31.123811+00:00
-- url     : https://prove2.me/theorems/6efbcf2b-c787-5ba5-abf3-a8c09ce77e6c
-- title:
--   Fractional Colouring: bdd Below weights
-- statement:
--   The set of fractional-colouring weights is bounded below by `0`.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L52-L55
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L52-L55

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Definitions.Def_FractionalLib_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}

theorem FractionalColouring.bddBelow_weights : BddBelow {t | ∃ x, IsFracColouring G x ∧ t = ∑ s, x s} := by sorry
