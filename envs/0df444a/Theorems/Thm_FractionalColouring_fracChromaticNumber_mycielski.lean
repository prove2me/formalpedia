-- Prove2me | Theorems.Thm_FractionalColouring_fracChromaticNumber_mycielski
-- name    : FractionalColouring.fracChromaticNumber_mycielski
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:36:28.641186+00:00
-- url     : https://prove2.me/theorems/73d453f8-f98c-4020-9509-6ac0d40f5ec0
-- title:
--   Fractional Colouring: frac Chromatic Number mycielski
-- statement:
--   **Larsen–Propp–Ullman (1995).** For every finite graph `G` with at least one vertex,
--   `χ_f(M(G)) = χ_f(G) + 1/χ_f(G)`.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L338-L340
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L338-L340

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
variable {G}
variable (G)

theorem FractionalColouring.fracChromaticNumber_mycielski [Nonempty V] :
    fracChromaticNumber (graph G) = fracChromaticNumber G + 1 / fracChromaticNumber G := by sorry
