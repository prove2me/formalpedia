-- Prove2me | Theorems.Thm_FractionalColouring_fracChromaticNumber_le
-- name    : FractionalColouring.fracChromaticNumber_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:29:35.689712+00:00
-- url     : https://prove2.me/theorems/cd740d2e-d9fb-5039-a823-aec6533d11c2
-- title:
--   Fractional Colouring: frac Chromatic Number le
-- statement:
--   Any fractional colouring weighs at least `χ_f(G)`.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L78-L80
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L78-L80

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

theorem FractionalColouring.fracChromaticNumber_le {x : Finset V → ℝ} (hx : IsFracColouring G x) :
    fracChromaticNumber G ≤ ∑ s, x s := by sorry
