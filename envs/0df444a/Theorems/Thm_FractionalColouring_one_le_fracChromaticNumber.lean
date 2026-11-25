-- Prove2me | Theorems.Thm_FractionalColouring_one_le_fracChromaticNumber
-- name    : FractionalColouring.one_le_fracChromaticNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:32:33.586676+00:00
-- url     : https://prove2.me/theorems/f6023a62-d891-4225-b76f-3091dc02501d
-- title:
--   Fractional Colouring: one le frac Chromatic Number
-- statement:
--   `1 ≤ χ_f(G)` on a nonempty vertex type.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L138-L144
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L138-L144

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

theorem FractionalColouring.one_le_fracChromaticNumber [Nonempty V] : 1 ≤ fracChromaticNumber G := by sorry
