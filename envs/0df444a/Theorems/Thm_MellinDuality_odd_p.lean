-- Prove2me | Theorems.Thm_MellinDuality_odd_p
-- name    : MellinDuality.odd_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:46.176261+00:00
-- url     : https://prove2.me/theorems/052537b6-c104-4244-8edf-ca96e79f989d
-- title:
--   Mellin Duality: odd p
-- statement:
--   The Mellin Duality construction uses the odd p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L25-L25
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L25-L25

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.odd_p (hp2 : p ≠ 2) : Odd p := by sorry
