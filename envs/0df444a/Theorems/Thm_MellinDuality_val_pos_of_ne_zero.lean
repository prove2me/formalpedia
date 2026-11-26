-- Prove2me | Theorems.Thm_MellinDuality_val_pos_of_ne_zero
-- name    : MellinDuality.val_pos_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:07.639229+00:00
-- url     : https://prove2.me/theorems/7c5c7e06-02b7-49da-b8a6-42adf6cb4928
-- title:
--   Mellin Duality: val pos of ne zero
-- statement:
--   The Mellin Duality construction uses the val pos of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L30-L31
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L30-L31

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.val_pos_of_ne_zero {x : ZMod p} (hx : x ≠ 0) : 0 < x.val := by sorry
