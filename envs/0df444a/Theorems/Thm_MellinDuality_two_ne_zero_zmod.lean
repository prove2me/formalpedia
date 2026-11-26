-- Prove2me | Theorems.Thm_MellinDuality_two_ne_zero_zmod
-- name    : MellinDuality.two_ne_zero_zmod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:44.824376+00:00
-- url     : https://prove2.me/theorems/2c82f0f6-e117-5042-b5d3-24cb94f5ef22
-- title:
--   Mellin Duality: two ne zero zmod
-- statement:
--   The Mellin Duality construction uses the two ne zero zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L112-L116
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L112-L116

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]

theorem MellinDuality.two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by sorry
