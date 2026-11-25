-- Prove2me | Theorems.Thm_FractionalColouring_weights_nonempty
-- name    : FractionalColouring.weights_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:29:32.413493+00:00
-- url     : https://prove2.me/theorems/32d44f97-3fef-5230-a0ea-dc75b7883a43
-- title:
--   Fractional Colouring: weights nonempty
-- statement:
--   The set of fractional-colouring weights is nonempty.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L74-L75
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L74-L75

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

theorem FractionalColouring.weights_nonempty : {t | ∃ x, IsFracColouring G x ∧ t = ∑ s, x s}.Nonempty := by sorry
