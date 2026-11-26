-- Prove2me | Theorems.Thm_MellinDuality_parSign_neg
-- name    : MellinDuality.parSign_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:45.29199+00:00
-- url     : https://prove2.me/theorems/a84d114d-3c47-4daa-9c2c-c6c2b455ed7c
-- title:
--   Mellin Duality: par Sign neg
-- statement:
--   The Mellin Duality construction uses the par Sign neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L41-L43
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L41-L43

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.parSign_neg (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) : parSign (-x) = -parSign x := by sorry
