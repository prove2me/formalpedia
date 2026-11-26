-- Prove2me | Theorems.Thm_MellinDuality_quad_cast_eq_pow
-- name    : MellinDuality.quad_cast_eq_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:48.867621+00:00
-- url     : https://prove2.me/theorems/2df45488-44fd-4b20-99fe-3abcd53ca619
-- title:
--   Mellin Duality: quad cast eq pow
-- statement:
--   The Mellin Duality construction uses the quad cast eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L133-L136
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L133-L136

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]

theorem MellinDuality.quad_cast_eq_pow (hp2 : p ≠ 2) (n : ZMod p) :
    ((quadraticChar (ZMod p) n : ℤ) : ZMod p) = n ^ (p / 2) := by sorry
