-- Prove2me | Theorems.Thm_FractionalColouring_le_fracChromaticNumber_mycielski
-- name    : FractionalColouring.le_fracChromaticNumber_mycielski
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:34:29.849629+00:00
-- url     : https://prove2.me/theorems/6f32d5a1-acf3-5224-8438-e6a8e93f16a7
-- title:
--   Fractional Colouring: le frac Chromatic Number mycielski
-- statement:
--   The Fractional Colouring construction uses the le frac Chromatic Number mycielski property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L317-L333
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L317-L333

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

theorem FractionalColouring.le_fracChromaticNumber_mycielski [Nonempty V] :
    fracChromaticNumber G + 1 / fracChromaticNumber G ≤ fracChromaticNumber (graph G) := by sorry
