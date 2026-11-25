-- Prove2me | Theorems.Thm_FractionalColouring_fracChromaticNumber_mycielski_le
-- name    : FractionalColouring.fracChromaticNumber_mycielski_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:34:18.557982+00:00
-- url     : https://prove2.me/theorems/7de912a5-f1be-535e-a610-298bdfd3b6ff
-- title:
--   Fractional Colouring: frac Chromatic Number mycielski le
-- statement:
--   The Fractional Colouring construction uses the frac Chromatic Number mycielski le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L215-L232
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L215-L232

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

theorem FractionalColouring.fracChromaticNumber_mycielski_le [Nonempty V] :
    fracChromaticNumber (graph G) ≤ fracChromaticNumber G + 1 / fracChromaticNumber G := by sorry
