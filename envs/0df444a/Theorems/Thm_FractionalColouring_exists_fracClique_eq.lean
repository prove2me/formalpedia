-- Prove2me | Theorems.Thm_FractionalColouring_exists_fracClique_eq
-- name    : FractionalColouring.exists_fracClique_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:32:31.568799+00:00
-- url     : https://prove2.me/theorems/0cd35b67-65a5-5f5e-9ec5-fca5f5536b4f
-- title:
--   Fractional Colouring: exists frac Clique eq
-- statement:
--   **Strong duality.** Some fractional clique weighs exactly `χ_f(G)`.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L148-L187
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L148-L187

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
open Classical

theorem FractionalColouring.exists_fracClique_eq : ∃ g, IsFracClique G g ∧ ∑ v, g v = fracChromaticNumber G := by sorry
